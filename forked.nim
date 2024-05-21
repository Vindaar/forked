import cligen / [procpool, mslice, osUt]
export osUt, mslice, procpool

import std / [macros, typetraits, os]
from std / strutils import parseInt
from std / osproc import countProcessors
export countProcessors, getEnv, parseInt, supportsCopyMem, `/`, getCurrentProcessId, dirExists, createDir

## Note: for now we use `supportsCopyMem`
#import ./needs_copy_impl
when isMainModule or defined(UseFlatBuffers):
  import flatBuffers
  export asFlat, flatTo, getSize
else:
  static: info "Make sure to import a library that provides `saveBuffer`, `loadBuffer` primitives if you use `forked`."

type
  JoinStmt = object
    n: NimNode
  SendStmt = object
    id: NimNode # identfier or expression to be sent
    n: NimNode
  IterStmt = object
    n: NimNode
    iter: NimNode ## the actual iterator
    jobs: NimNode

## Decides if we send data from child processes back to the parent by producing (in memory)
## files using `/dev/shm` (or real files if `BasePath` is changed)
const WriteFiles* {.booldefine.} = true
## Decides if the binary data files are deleted upon being memory mapped by the parent
const DeleteFiles* {.booldefine.} = true
## Can be used to change the default path where binary files are stored
const BasePath* {.strdefine.} = "/dev/shm/pp_forked/"

template send*(oSym, idxSym, arg: untyped): untyped {.dirty.} =
  ## This template takes care of writing data from each job back to the main process
  #echo "TYPE: ", typeof(arg), " support?", typeof(arg).supportsCopyMem
  when not typeof(arg).supportsCopyMem: #needsCopy:
    when WriteFiles:
      # We create a path based on the current PID. Because this runs in the forked process, it means
      # each process has its own dir!
      let dir = BasePath / "pid_" & $getCurrentProcessId()
      if not dirExists(dir):
        createDir(dir)
      let path = dir / "job_" & $idxSym & ".dat"
      arg.saveBuffer(path)
      let n = path.len
      discard oSym.uriteBuffer(n.addr, n.sizeof) # could use a different way to write, but would need other `frame*` logic
      discard oSym.uriteBuffer(path[0].addr, n)
    else:
      let buf = asFlat(arg)
      let n   = buf.size
      discard oSym.uriteBuffer(n.addr, n.sizeof)
      discard oSym.uriteBuffer(buf.data, buf.size)
  else:
    discard oSym.uWr(arg)

## The two helper templates which produce the correct procpool, depending on the
## data types used
template ppFramesOb(R, W, oSym, sSym, idxSym, jobs, body: untyped): untyped =
  initProcPool( (
    proc(r, w: cint) =
      let i = open(r)
      let oSym = open(w, fmWrite)
      var `sSym Tup`: R # R is (int, UserType)
      while i.uRd(`sSym Tup`):
        let (idxSym, sSym) = `sSym Tup`
        body
  ), framesOb, jobs, aux = sizeof(W))

template ppFramesLenPfx(R, W, oSym, sSym, idxSym, jobs, body: untyped): untyped =
  initProcPool( (
    proc(r, w: cint) =
      let i = open(r)
      let oSym = open(w, fmWrite)
      var `sSym Tup`: R # R is (int, UserType)
      while i.uRd(`sSym Tup`):
        let (idxSym, sSym) = `sSym Tup`
        body
  ), framesLenPfx, jobs)

proc extractJoin(n: NimNode): JoinStmt =
  ## Extract the `finally:` statement from the ForLoop
  doAssert n.kind == nnkForStmt
  doAssert n.len == 3
  doAssert n[2].kind == nnkStmtList
  let body = n[2]
  let join = body[body.len-1]
  if join.kind notin {nnkCall, nnkCommand} and
    join[0].kind != nnkIdent and join[0].strVal != "join":
    error("The last stmt inside the `forked` for loop must be a `join` statement! Is: " & $body[body.len-1].treerepr)
  result = JoinStmt(n: join[1])

proc extractSend(n: NimNode): SendStmt =
  ## Extract the `send` statement from the ForLoop
  doAssert n.kind == nnkForStmt
  doAssert n.len == 3
  doAssert n[2].kind == nnkStmtList
  let body = n[2]
  if body[body.len-2].kind notin {nnkCommand, nnkCall}:
    error("The second to last stmt inside the `forked` for loop must be a `send foo` stmt!")
  let sen = body[body.len-2]
  doAssert sen[0].kind in {nnkSym, nnkIdent} and sen[0].strVal == "send"
  result = SendStmt(n: sen, id: sen[1])

proc extractBody(n: NimNode): NimNode =
  ## Extract the actual body of the ForLoop that should run for each job
  doAssert n.kind == nnkForStmt
  doAssert n.len == 3
  doAssert n[2].kind == nnkStmtList
  let body = n[2]
  result = newStmtList()
  for i in 0 ..< body.len - 2:
    result.add body[i]

proc extractIter(n: NimNode): IterStmt =
  ## Extract the actual iterator we iterate over, as well as the, unfortunately needed
  ## output type information
  doAssert n.kind == nnkForStmt
  let call = n[1]
  doAssert call.kind == nnkCall and call[0].kind == nnkIdent and
    call[0].strVal == "forked", "For loop argument must be a `forked` call"
  var jobs = newLit 0
  case call.len
  of 2: discard # all good
  of 3: jobs = call[2] # get number of jobs from last argument
  else:
    error("Must be length 2, (forked, iter). Got: " & $call.treerepr)
  result = IterStmt(n: n, iter: call[1], jobs: jobs)

proc replaceSymbol(n: NimNode, arg, by: NimNode): NimNode =
  ## Helper to replace a symbol `arg` by `by` in the given
  ## NimNode `n`
  proc finish(n: NimNode, arg, by: NimNode): NimNode =
    case n.kind
    of nnkIdent:
      if n.strVal == arg.strVal: result = by
      else: result = n
    else:
      if n.len == 0: result = n
      else:
        result = newTree(n.kind)
        for ch in n:
          result.add finish(ch, arg, by)
  result = finish(n, arg, by)

proc finalizeJoin(fn: JoinStmt, send: SendStmt, outTyp, joinId: NimNode): NimNode =
  ## Replace the `send` identifier by a correct pointer cast / load from buffer
  ## setup
  let sl = genSym(nskParam, "slice") ## XXX: update
  let by = quote do:
    when not `outTyp`.supportsCopyMem:
      when WriteFiles:
        let path = $(`sl`)
        loadBuffer[`outTyp`](path, DeleteFiles)
      else:
        let buf = newBuf(`sl`.mem, `sl`.len)
        flatTo[`outTyp`](buf)
    else:
      cast[ptr `outTyp`](`sl`.mem)[]
  result = replaceSymbol(fn.n, send.id, by)
  result = quote do: # produce the final template, arg to `onReply`
    template `joinId`(`sl`: MSlice) =
      `result`

proc patchSendTmpl(sen: SendStmt, oId, idxSym: NimNode): NimNode =
  ## Mutate `n` to patch the `send Foo` to be `send oId, Foo`
  result = nnkCommand.newTree(ident"send", oId, idxSym, sen.id)

macro forked*(n: ForLoopStmt): untyped =
  ## XXX: Extend to not force `evalOb` and `uRd` on the input side! Also allow copy & load there
  # Extract all the relevant pieces of the for loop stmt
  let iter = extractIter(n)
  let join = extractJoin(n)
  let sen  = extractSend(n)
  var body = extractBody(n)
  let sId  = n[0] # iterator variable ## TODO: allow pair of (i, x)

  # Define the symbols to use in the generated code
  let oId    = genSym(nskLet, "o")
  let joinId = genSym(nskTemplate, "join")
  let ppId   = genSym(nskVar, "pp")
  let idxSym = genSym(nskLet, "idx")

  # Get iterator and symbol of output type
  let iterCall = iter.iter
  let Wid      = genSym(nskType, "W") # write type

  # Produce a "fake" body that we use to determine the type of the
  # data we `send`
  var fakeBody = quote do:
    type RIn = typeof(`iterCall`)
    var `sId`: RIn
  fakeBody.add body.copy()
  let senId = sen.id
  fakeBody.add senId

  # finalize the `join` `onReply` logic
  let finJoin  = finalizeJoin(join, sen, Wid, joinId)

  # finalize the body (i.e. patch `send` template)
  body.add patchSendTmpl(sen, oId, idxSym)
  let jobs = iter.jobs
  result = quote do:
    type RIn = typeof(`iterCall`)
    type R = (int, RIn)
    type `WId` = typeof(`fakeBody`)
    let jobs = if `jobs` > 0: `jobs` else: parseInt(getEnv("PP_JOBS", $countProcessors()))
    when not `WId`.supportsCopyMem:
      var `ppId` = ppFramesLenPfx(R, `WId`, `oId`, `sId`, `idxSym`, jobs, `body`)
    else:
      var `ppId` = ppFramesOb(R, `WId`, `oId`, `sId`, `idxSym`, jobs, `body`)
    `finJoin`
    iterator inner(): R =
      var idx = 0
      for x in `iterCall`:
        yield (idx, x)
        inc idx
    `ppId`.evalOb inner(), `joinId`
  when defined(DEBUG_FORKED):
    echo "Result:\n", result.repr

when isMainModule:
  proc term(k: int): float = (0.5 - float(k mod 2))*8'f/float(2*k + 1)

  iterator batches(n, batch: int): Slice[int] =
    for start in countup(0, n - 1, batch):
      yield start ..< start+batch

  proc piProcPool(n: int): float =
    for s in forked(batches(n, 5)):
      var res = 0.0
      for k in s:
        res += term(k)
      send res
      join: result += res

  type
    Foo = object
      s: string
      x: float

  proc calcFoo(x: int): Foo = Foo(s: $x, x: x.float)
  proc testIt(): seq[Foo] =
    for x in forked(0 ..< 10):
      let f = calcFoo(x)
      send f
      join: result.add f

  echo piProcPool(100)
  echo testIt()
