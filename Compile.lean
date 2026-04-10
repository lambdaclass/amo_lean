/-
  trzk — Compile Spec files to C/Rust

  Usage: .lake/build/bin/trzk <spec.lean> [--target c|rust] [--output <file>]
                                          [--name <funcname>] [--hardware scalar|neon|avx2]
-/

structure CompileConfig where
  specFile : Option String := none
  target : String := "c"
  output : Option String := none
  funcName : String := "spec"
  hardware : String := "scalar"
  help : Bool := false

partial def parseArgs : List String → CompileConfig → CompileConfig
  | [], cfg => cfg
  | "--target" :: v :: rest, cfg => parseArgs rest { cfg with target := v }
  | "--output" :: v :: rest, cfg => parseArgs rest { cfg with output := some v }
  | "--name" :: v :: rest, cfg => parseArgs rest { cfg with funcName := v }
  | "--hardware" :: v :: rest, cfg => parseArgs rest { cfg with hardware := v }
  | "--help" :: rest, cfg => parseArgs rest { cfg with help := true }
  | v :: rest, cfg =>
    if cfg.specFile.isNone && !v.startsWith "--"
    then parseArgs rest { cfg with specFile := some v }
    else parseArgs rest cfg

def showHelp : IO Unit := do
  IO.println "trzk — Compile algorithm specs to C/Rust"
  IO.println ""
  IO.println "Usage: .lake/build/bin/trzk <spec.lean> [options]"
  IO.println ""
  IO.println "Options:"
  IO.println "  --target c|rust          Target language (default: c)"
  IO.println "  --output <file>          Output file path (default: <spec>.c or <spec>.rs)"
  IO.println "  --name <funcname>        Function name in generated code (default: \"spec\")"
  IO.println "  --hardware scalar|neon|avx2  Hardware target for NTT optimization (default: scalar)"
  IO.println "  --help                   Show this help"
  IO.println ""
  IO.println "Spec file must define:  def spec : Spec := ..."
  IO.println ""
  IO.println "Examples:"
  IO.println "  def spec := ntt .babybear 1024"
  IO.println "  def spec := poseidon2Sbox .goldilocks 12"
  IO.println "  def spec := compose (kron (dft 2) (Spec.identity 2)) (kron (Spec.identity 2) (dft 2))"

def stripImports (source : String) : String :=
  let lines := source.splitOn "\n"
  let filtered := lines.filter fun line =>
    !(line.trimLeft.startsWith "import ")
  String.intercalate "\n" filtered

def buildRunner (userCode : String) (target : String) (funcName : String)
    (outputPath : String) (hardware : String) (artifactsDir : String)
    (baseName : String) : String :=
  let hwEnum := match hardware with
    | "neon" => ".neon"
    | "avx2" => ".avx2"
    | _      => ".scalar"
  s!"import AmoLean.CompileSpec
import AmoLean.Spec

open AmoLean.Spec
open AmoLean.CompileSpec (compileSpec)

{userCode}

def main : IO Unit := do
  IO.FS.createDirAll \"{artifactsDir}\"
  IO.FS.writeFile \"{artifactsDir}/{baseName}.spec\" (toString (repr spec))
  match compileSpec spec \"{target}\" {hwEnum} \"{funcName}\" with
  | .ok code =>
    IO.FS.writeFile \"{outputPath}\" code
  | .error msg =>
    (← IO.getStderr).putStrLn s!\"Error: \{msg}\"
    IO.Process.exit 1
"

def dirOf (path : String) : String :=
  match path.splitOn "/" |>.dropLast with
  | [] => "."
  | parts => String.intercalate "/" parts

def stemOf (path : String) : String :=
  let filename := match path.splitOn "/" with
    | [] => path
    | parts => parts.getLast!
  if filename.endsWith ".c" then filename.dropRight 2
  else if filename.endsWith ".rs" then filename.dropRight 3
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

  if cfg.target != "c" && cfg.target != "rust" then
    IO.eprintln s!"Error: unknown target '{cfg.target}'. Use 'c' or 'rust'."
    return 1

  if cfg.hardware != "scalar" && cfg.hardware != "neon" && cfg.hardware != "avx2" then
    IO.eprintln s!"Error: unknown hardware '{cfg.hardware}'. Use 'scalar', 'neon', or 'avx2'."
    return 1

  let outputPath := match cfg.output with
    | some p => p
    | none =>
      let ext := if cfg.target == "rust" then ".rs" else ".c"
      let base := if specFile.endsWith ".lean"
        then specFile.dropRight 5
        else specFile
      base ++ ext

  let outputDir := dirOf outputPath
  let artifactsDir := s!"{outputDir}/artifacts"
  let baseName := stemOf outputPath

  unless (← System.FilePath.pathExists ⟨specFile⟩) do
    IO.eprintln s!"Error: file '{specFile}' not found."
    return 1
  let userCode ← IO.FS.readFile ⟨specFile⟩
  let cleanCode := stripImports userCode

  let runner := buildRunner cleanCode cfg.target cfg.funcName outputPath
    cfg.hardware artifactsDir baseName

  let tmpPath := "/tmp/trzk_runner.lean"
  IO.FS.writeFile ⟨tmpPath⟩ runner

  let result ← IO.Process.output {
    cmd := "lake"
    args := #["env", "lean", "--run", tmpPath]
  }

  try IO.FS.removeFile ⟨tmpPath⟩ catch _ => pure ()

  if result.exitCode != 0 then
    IO.eprintln "Compilation failed:"
    IO.eprintln result.stderr
    return 1

  IO.println s!"Generated: {outputPath}"
  IO.println s!"Artifacts: {artifactsDir}/"
  return 0
