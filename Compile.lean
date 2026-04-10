/-
  trzk — Compile MatExpr specs to C/Rust

  Usage: .lake/build/bin/trzk <spec.lean> [--target c|rust] [--output <file>] [--name <funcname>]
-/

structure CompileConfig where
  specFile : Option String := none
  target : String := "c"
  output : Option String := none
  funcName : String := "spec"
  help : Bool := false

partial def parseArgs : List String → CompileConfig → CompileConfig
  | [], cfg => cfg
  | "--target" :: v :: rest, cfg => parseArgs rest { cfg with target := v }
  | "--output" :: v :: rest, cfg => parseArgs rest { cfg with output := some v }
  | "--name" :: v :: rest, cfg => parseArgs rest { cfg with funcName := v }
  | "--help" :: rest, cfg => parseArgs rest { cfg with help := true }
  | v :: rest, cfg =>
    if cfg.specFile.isNone && !v.startsWith "--"
    then parseArgs rest { cfg with specFile := some v }
    else parseArgs rest cfg

def showHelp : IO Unit := do
  IO.println "trzk — Compile MatExpr specs to C/Rust"
  IO.println ""
  IO.println "Usage: .lake/build/bin/trzk <spec.lean> [options]"
  IO.println ""
  IO.println "Options:"
  IO.println "  --target c|rust    Target language (default: c)"
  IO.println "  --output <file>    Output file path (default: <spec>.c or <spec>.rs)"
  IO.println "  --name <funcname>  Function name in generated code (default: \"spec\")"
  IO.println "  --help             Show this help"
  IO.println ""
  IO.println "Spec file must define:  def spec : MatExpr Int m n := ..."

/-- Remove `import` lines from user code (the runner provides its own imports). -/
def stripImports (source : String) : String :=
  let lines := source.splitOn "\n"
  let filtered := lines.filter fun line =>
    !(line.trimLeft.startsWith "import ")
  String.intercalate "\n" filtered

/-- Construct the runner source that wraps user code with imports and codegen. -/
def buildRunner (userCode : String) (target : String) (funcName : String)
    (outputPath : String) : String :=
  let (codegenImport, codegenOpen, codegenFn) := match target with
    | "rust" =>
      ("import AmoLean.Backends.Rust",
       "open AmoLean.Backends.Rust (matExprToRust)",
       "matExprToRust")
    | _ =>
      ("import AmoLean.Sigma.CodeGen",
       "open AmoLean.Sigma.CodeGen (matExprToC)",
       "matExprToC")
  s!"{codegenImport}
import AmoLean.Matrix.Basic

open AmoLean.Matrix (MatExpr)
{codegenOpen}

{userCode}

def main : IO Unit := do
  let code := {codegenFn} \"{funcName}\" _ _ spec
  IO.FS.writeFile \"{outputPath}\" code
"

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

  if cfg.target != "c" && cfg.target != "rust" then
    IO.eprintln s!"Error: unknown target '{cfg.target}'. Use 'c' or 'rust'."
    return 1

  -- Derive output path: use --output if given, otherwise replace .lean extension with .c/.rs
  let outputPath := match cfg.output with
    | some p => p
    | none =>
      let ext := if cfg.target == "rust" then ".rs" else ".c"
      let base := if specFile.endsWith ".lean"
        then specFile.dropRight 5
        else specFile
      base ++ ext

  -- Read spec file
  unless (← System.FilePath.pathExists ⟨specFile⟩) do
    IO.eprintln s!"Error: file '{specFile}' not found."
    return 1
  let userCode ← IO.FS.readFile ⟨specFile⟩

  -- Build runner
  let cleanCode := stripImports userCode
  let runner := buildRunner cleanCode cfg.target cfg.funcName outputPath

  -- Write temp runner file
  let tmpPath := "/tmp/trzk_runner.lean"
  IO.FS.writeFile ⟨tmpPath⟩ runner

  -- Run lean on the runner
  let result ← IO.Process.output {
    cmd := "lake"
    args := #["env", "lean", "--run", tmpPath]
  }

  -- Clean up temp file
  try IO.FS.removeFile ⟨tmpPath⟩ catch _ => pure ()

  if result.exitCode != 0 then
    IO.eprintln "Compilation failed:"
    IO.eprintln result.stderr
    return 1

  IO.println s!"Generated: {outputPath}"
  return 0
