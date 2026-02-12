/-
  AMO-Lean Protocols Module

  Cryptographic protocol implementations:
  - FRI: Fast Reed-Solomon IOP (Commit Phase) - STABLE
  - Poseidon: [FUTURE] ZK-friendly hash function

  Each protocol uses Core for algebra and Backends for code generation.
-/

-- FRI Protocol (stable, verified)
import AmoLean.FRI.Basic
import AmoLean.FRI.Fold
import AmoLean.FRI.Protocol
import AmoLean.FRI.Transcript
import AmoLean.FRI.Merkle
import AmoLean.FRI.Kernel
import AmoLean.FRI.CodeGen

-- Future protocols will be imported here:
-- import AmoLean.Protocols.Poseidon
