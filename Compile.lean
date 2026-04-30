/-
  trzk — Compile ArithExpr specs to Rust via optisat saturation.

  Usage: .lake/build/bin/trzk <spec.lean> [--output <file>] [--name <funcname>]
-/

structure CompileConfig where
  specFile : Option String := none
  output   : Option String := none
  funcName : String := "arith_spec"
  help     : Bool := false

partial def parseArgs : List String → CompileConfig → CompileConfig
  | [], cfg => cfg
  | "--output" :: v :: rest, cfg => parseArgs rest { cfg with output := some v }
  | "--name"   :: v :: rest, cfg => parseArgs rest { cfg with funcName := v }
  | "--help"   :: rest, cfg => parseArgs rest { cfg with help := true }
  | v :: rest, cfg =>
    if cfg.specFile.isNone && !v.startsWith "--"
    then parseArgs rest { cfg with specFile := some v }
    else parseArgs rest cfg

def showHelp : IO Unit := do
  IO.println "trzk — Compile ArithExpr specs to Rust"
  IO.println ""
  IO.println "Usage: .lake/build/bin/trzk <spec.lean> [options]"
  IO.println ""
  IO.println "Options:"
  IO.println "  --output <file>    Output file path (default: <spec>.rs)"
  IO.println "  --name <funcname>  Function name in generated code (default: arith_spec)"
  IO.println "  --help             Show this help"
  IO.println ""
  IO.println "Spec file must define:  def spec : ArithExpr := ..."

/-- Remove `import` lines from user code; the runner provides its own imports. -/
def stripImports (source : String) : String :=
  let lines := source.splitOn "\n"
  let filtered := lines.filter fun line =>
    !(line.trimLeft.startsWith "import ")
  String.intercalate "\n" filtered

/-- Build the runner source: imports TRZK, inlines user code, calls the pipeline,
    emits Rust, and dumps pre/post-saturation ArithExpr into artifacts/. -/
def buildRunner (userCode funcName outputPath artifactsDir baseName : String) : String :=
  s!"import TRZK

open TRZK

{userCode}

def main : IO Unit := do
  IO.FS.createDirAll \"{artifactsDir}\"
  IO.FS.writeFile \"{artifactsDir}/{baseName}.pre.txt\" (toString (repr spec))
  let arity := spec.inputArity
  match optimize spec with
  | none =>
    IO.eprintln \"optimize returned none\"
    IO.Process.exit 1
  | some post =>
    IO.FS.writeFile \"{artifactsDir}/{baseName}.post.txt\" (toString (repr post))
    let code := emitFunction \"{funcName}\" arity post
    IO.FS.writeFile \"{outputPath}\" code
"

def dirOf (path : String) : String :=
  match path.splitOn "/" |>.dropLast with
  | [] => "."
  | parts => String.intercalate "/" parts

def stemOf (path : String) : String :=
  let filename := match path.splitOn "/" with
    | [] => path
    | parts => parts.getLast!
  if filename.endsWith ".rs" then filename.dropRight 3
  else if filename.endsWith ".lean" then filename.dropRight 5
  else filename

def main (args : List String) : IO UInt32 := do
  let cfg := parseArgs args {}

  if cfg.help then
    showHelp
    return 0

  let specFile ← match cfg.specFile with
    | some f => pure f
    | none =>
      IO.eprintln "Error: no spec file provided."
      IO.eprintln "Run with --help for usage."
      return 1

  let outputPath := match cfg.output with
    | some p => p
    | none =>
      let base := if specFile.endsWith ".lean" then specFile.dropRight 5 else specFile
      base ++ ".rs"

  let outputDir := dirOf outputPath
  let artifactsDir := s!"{outputDir}/artifacts"
  let baseName := stemOf outputPath

  unless (← System.FilePath.pathExists ⟨specFile⟩) do
    IO.eprintln s!"Error: file '{specFile}' not found."
    return 1
  let userCode ← IO.FS.readFile ⟨specFile⟩
  let cleanCode := stripImports userCode
  let runner := buildRunner cleanCode cfg.funcName outputPath artifactsDir baseName

  let tmpPath := "/tmp/trzk_runner.lean"
  IO.FS.writeFile ⟨tmpPath⟩ runner

  let result ← IO.Process.output {
    cmd := "lake"
    args := #["env", "lean", "--run", tmpPath]
  }

  try IO.FS.removeFile ⟨tmpPath⟩ catch _ => pure ()

  if result.exitCode != 0 then
    IO.eprintln "Compilation failed:"
    IO.eprintln s!"--- stderr ---\n{result.stderr}"
    IO.eprintln s!"--- stdout ---\n{result.stdout}"
    return 1

  IO.println s!"Generated: {outputPath}"
  IO.println s!"IR:        {artifactsDir}/{baseName}.\{pre,post}.txt"
  return 0
