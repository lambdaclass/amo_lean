/-
  Generate fri_fold.h from VecCodeGen
-/

import AmoLean.Vector.CodeGen

open AmoLean.Vector.CodeGen

def main : IO Unit := do
  let config : CodeGenConfig := {}
  let content := generateFriHeader config
  IO.FS.writeFile "generated/fri_fold.h" content
  IO.println "Generated: generated/fri_fold.h"
