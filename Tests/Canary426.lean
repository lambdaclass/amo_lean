-- Tests/Canary426.lean — Verifica que todos los imports críticos resuelven en 4.26
-- Si este archivo compila, los paths de import principales son válidos.

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Basic

#check Nat.Prime
#check ZMod
#check Finset.sum
#check @ring_nf
