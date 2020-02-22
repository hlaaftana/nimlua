# mostly stolen from nlvm

import luagen

import
  compiler/[
    ast,
    cmdlinehelper,
    commands,
    condsyms,
    extccomp,
    idents,
    idgen,
    lexer,
    lineinfos,
    llstream,
    modulegraphs,
    modules,
    msgs,
    options,
    passes,
    passaux,
    pathutils,
    platform,
    sem,
    syntaxes
  ],
  parseopt,
  strutils,
  times,
  os,
  tables

const
  NimLuaVersion = "0.1.0"
  #NimLuaHash = gorge("git rev-parse HEAD").strip
  #NimHash = gorge("git -C ../Nim rev-parse HEAD").strip

  HelpHeader = """Nim to lua compiler, version $1 [$2: $3]
Nim compiler (c) 2009-2019 Andreas Rumpf
"""

proc helpHeader(conf: ConfigRef): string =
  HelpHeader % [
    NimLuaVersion,
    platform.OS[conf.target.hostOS].name,
    platform.CPU[conf.target.hostCPU].name]

proc writeVersionInfo(conf: ConfigRef; pass: TCmdLinePass) =
  if pass == passCmd1:
    msgWriteln(conf, helpHeader(conf), {msgStdout})

    msgWriteln(conf, "NimLua: " & NimLuaVersion, {msgStdout})
    msgWriteln(conf, "Nim: " & NimVersion, {msgStdout})

    msgQuit(0)

proc addPrefix(switch: string): string =
  if len(switch) == 1: result = "-" & switch
  else: result = "--" & switch

proc expectNoArg(
    conf: ConfigRef; switch, arg: string, pass: TCmdLinePass, info: TLineInfo) =
  if arg != "":
    localError(
      conf, info,
      "invalid argument for command line option: '$1'" % addPrefix(switch))

proc processSwitch(switch, arg: string, pass: TCmdLinePass,
    info: TLineInfo, conf: ConfigRef) =
  # stolen from nlvm
  case switch.normalize
  of "version", "v":
    expectNoArg(conf, switch, arg, pass, info)
    writeVersionInfo(conf, pass)
  else:
    commands.processSwitch(switch, arg, pass, info, conf)

proc processSwitch*(pass: TCmdLinePass; p: OptParser; config: ConfigRef) =
  # stolen from nlvm
  var bracketLe = strutils.find(p.key, '[')
  if bracketLe >= 0:
    var key = substr(p.key, 0, bracketLe - 1)
    var val = substr(p.key, bracketLe) & ':' & p.val
    processSwitch(key, val, pass, gCmdLineInfo, config)
  else:
    processSwitch(p.key, p.val, pass, gCmdLineInfo, config)

proc processCmdLine(pass: TCmdLinePass, cmd: string; config: ConfigRef) =
  var p = parseopt.initOptParser(cmd)
  var argsCount = 0
  while true:
    parseopt.next(p)
    case p.kind
    of cmdEnd: break
    of cmdLongoption, cmdShortOption:
      if p.key == " ":
        p.key = "-"
        if processArgument(pass, p, argsCount, config): break
      else:
        processSwitch(pass, p, config)
    of cmdArgument:
      if processArgument(pass, p, argsCount, config): break
  if pass == passCmd2:
    if optRun notin config.globalOptions and config.arguments.len > 0 and config.command.normalize != "run":
      rawMessage(config, errGenerated, errArgsNeedRunOption)

proc semanticPasses(g: ModuleGraph) =
  registerPass g, verbosePass
  registerPass g, semPass

proc writeDepsFile(g: ModuleGraph) =
  let fname = g.config.nimcacheDir / RelativeFile(g.config.projectName & ".deps")
  let f = open(fname.string, fmWrite)
  for m in g.modules:
    if m != nil:
      f.writeLine(toFullPath(g.config, m.position.FileIndex))
  for k in g.inclToMod.keys:
    if g.getModule(k).isNil:  # don't repeat includes which are also modules
      f.writeLine(toFullPath(g.config, k))
  f.close()

proc compileSystemModule(graph: ModuleGraph) =
  graph.connectCallbacks()
  graph.config.m.systemFileIdx = fileInfoIdx(graph.config,
      graph.config.prefixDir / RelativeFile"lualib/system.nim")
  discard graph.compileModule(graph.config.m.systemFileIdx, {sfSystemModule})

proc commandCompile(graph: ModuleGraph) =
  let conf = graph.config

  if conf.outDir.isEmpty:
    conf.outDir = conf.projectPath
  if conf.outFile.isEmpty:
    conf.outFile = RelativeFile(conf.projectName & ".lua")

  #incl(gGlobalOptions, optSafeCode)
  setTarget(graph.config.target, osJS, cpuJS)
  #initDefines()
  defineSymbol(graph.config.symbols, "js")
  defineSymbol(graph.config.symbols, "lua")
  semanticPasses(graph)
  registerPass(graph, luagenPass)
  compileSystemModule(graph)
  wantMainModule(conf)
  let projectFile = conf.projectMainIdx
  graph.importStack.add projectFile
  discard graph.compileModule(projectFile, {sfMainModule})
  if optGenScript in graph.config.globalOptions:
    writeDepsFile(graph)

proc commandScan(conf: ConfigRef) =
  var f = addFileExt(mainCommandArg(conf), NimExt)
  var stream = llStreamOpen(f.AbsoluteFile, fmRead)
  if stream != nil:
    var
      L: TLexer
      tok: TToken
    initToken(tok)
    openLexer(L, f.AbsoluteFile, stream, newIdentCache(), conf)
    while true:
      rawGetTok(L, tok)
      conf.printTok(tok)
      if tok.tokType == tkEof: break
    closeLexer(L)
  else:
    conf.rawMessage(errCannotOpenFile, f)

proc commandCheck(graph: ModuleGraph) =
  graph.config.errorMax = high(int)  # do not stop after first error
  defineSymbol(graph.config.symbols, "nimcheck")
  semanticPasses(graph)  # use an empty backend for semantic checking only
  compileProject(graph)

proc mainCommand*(graph: ModuleGraph) =
  let conf = graph.config

  conf.lastCmdTime = epochTime()
  conf.searchPaths.add(conf.libpath)

  # No support! but it might work anyway :)
  conf.globalOptions.excl optTlsEmulation

  setId(193)

  case conf.command.normalize
  # Take over the default compile command
  of "c", "cc", "lua", "compile", "compiletolua":
    conf.cmd = cmdCompileToJs
    commandCompile(graph)
  of "dump":
    conf.msgWriteln("-- list of currently defined symbols --")
    for s in definedSymbolNames(conf.symbols): conf.msgWriteln(s)
    conf.msgWriteln("-- end of list --")

    for it in conf.searchPaths: conf.msgWriteln(it.string)

  of "scan":
    conf.cmd = cmdScan
    conf.wantMainModule()
    commandScan(conf)

  of "check":
    conf.cmd = cmdCheck
    commandCheck(graph)

  else: conf.rawMessage(errGenerated, conf.command)

  if conf.errorCounter == 0 and
      conf.cmd notin {cmdInterpret, cmdRun, cmdDump}:
    when declared(system.getMaxMem):
      let usedMem = formatSize(getMaxMem()) & " peakmem"
    else:
      let usedMem = formatSize(getTotalMem())
    rawMessage(conf, hintSuccessX, [$conf.linesCompiled,
                formatFloat(epochTime() - conf.lastCmdTime, ffDecimal, 3),
                usedMem,
                if isDefined(conf, "release"): "Release Build"
                else: "Debug Build"])

proc handleCmdLine(cache: IdentCache, conf: ConfigRef) =
  # For now, we reuse the nim command line options parser, mainly because
  # the options are used all over the compiler, but also because we want to
  # act as a drop-in replacement (for now)
  # Most of this is taken from the main nim command
  let self = NimProg(
    supportsStdinFile: true,
    processCmdLine: processCmdLine,
    mainCommand: mainCommand
  )
  self.initDefinesProg(conf, "nimlua")

  if paramCount() == 0:
    writeVersionInfo(conf, passCmd1)
    return

  self.processCmdLineAndProjectPath(conf)

  if not self.loadConfigsAndRunMainCommand(cache, conf):
    return
  if conf.errorCounter != 0:
    return

  if optRun in conf.globalOptions:
    let ex = quoteShell conf.absOutFile
    execExternalProgram(conf, findExe("lua") & ' ' & ex & ' ' & conf.arguments)

let
  conf = newConfigRef()
  cache = newIdentCache()

when false:
  var tmp = getAppDir()
  while not dirExists(tmp / "NimLua-lib") and tmp.len > 1:
    tmp = tmp.parentDir()

  conf.prefixDir = AbsoluteDir(tmp / "Nim")
  conf.searchPaths.insert(conf.prefixDir / RelativeDir"../NimLua-lib", 0)

handleCmdLine(cache, conf)