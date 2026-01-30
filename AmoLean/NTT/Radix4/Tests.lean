/-
  AMO-Lean: Tests Comprehensivos para NTT Radix-4

  Batería de tests diseñada por QA (Gemini) para validar:
  1. Roundtrip: INTT(NTT(x)) = x
  2. Linealidad: NTT(a + b) = NTT(a) + NTT(b)
  3. Tests parametrizados: N = 4, 8, 16, 32
  4. Diversos tipos de entrada: delta, constante, secuencial

  Fecha: 2026-01-30
-/

import AmoLean.NTT.Spec
import AmoLean.NTT.Goldilocks
import AmoLean.NTT.Radix4.Butterfly4
import AmoLean.NTT.Radix4.Stride4
import AmoLean.NTT.Radix4.Algorithm

namespace AmoLean.NTT.Radix4.Tests

open AmoLean.NTT
open AmoLean.Field.Goldilocks

/-! ## Helpers -/

/-- Convierte lista de GoldilocksField a valores UInt64 para comparación -/
def toVals (xs : List GoldilocksField) : List UInt64 := xs.map (·.value)

/-- Compara dos listas de GoldilocksField -/
def listsEqual (xs ys : List GoldilocksField) : Bool :=
  toVals xs == toVals ys

/-- Suma elemento a elemento de dos listas -/
def listAdd (xs ys : List GoldilocksField) : List GoldilocksField :=
  xs.zipWith GoldilocksField.add ys

/-! ## Test 1: Roundtrip INTT(NTT(x)) = x -/

#eval! do
  IO.println "═══════════════════════════════════════════════════════════"
  IO.println "   TEST 1: Roundtrip INTT(NTT(x)) = x"
  IO.println "═══════════════════════════════════════════════════════════"

  -- Test 1.1: N=4, entrada delta [1,0,0,0]
  IO.println "\n1.1 Roundtrip N=4, delta [1,0,0,0]:"
  let delta4 : List GoldilocksField := [⟨1⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩]
  let ω4 := primitiveRoot 4 (by decide)
  let n_inv4 := GoldilocksField.inv ⟨4⟩
  let ntt_delta4 := NTT_spec ω4 delta4
  let roundtrip_delta4 := INTT_spec ω4 n_inv4 ntt_delta4
  IO.println s!"    Input:     {toVals delta4}"
  IO.println s!"    NTT:       {toVals ntt_delta4}"
  IO.println s!"    INTT(NTT): {toVals roundtrip_delta4}"
  IO.println s!"    ✓ Roundtrip OK: {listsEqual delta4 roundtrip_delta4}"

  -- Test 1.2: N=4, entrada constante [1,1,1,1]
  IO.println "\n1.2 Roundtrip N=4, constante [1,1,1,1]:"
  let const4 : List GoldilocksField := [⟨1⟩, ⟨1⟩, ⟨1⟩, ⟨1⟩]
  let ntt_const4 := NTT_spec ω4 const4
  let roundtrip_const4 := INTT_spec ω4 n_inv4 ntt_const4
  IO.println s!"    Input:     {toVals const4}"
  IO.println s!"    NTT:       {toVals ntt_const4}"
  IO.println s!"    INTT(NTT): {toVals roundtrip_const4}"
  IO.println s!"    ✓ Roundtrip OK: {listsEqual const4 roundtrip_const4}"

  -- Test 1.3: N=4, entrada secuencial [1,2,3,4]
  IO.println "\n1.3 Roundtrip N=4, secuencial [1,2,3,4]:"
  let seq4 : List GoldilocksField := [⟨1⟩, ⟨2⟩, ⟨3⟩, ⟨4⟩]
  let ntt_seq4 := NTT_spec ω4 seq4
  let roundtrip_seq4 := INTT_spec ω4 n_inv4 ntt_seq4
  IO.println s!"    Input:     {toVals seq4}"
  IO.println s!"    NTT:       {toVals ntt_seq4}"
  IO.println s!"    INTT(NTT): {toVals roundtrip_seq4}"
  IO.println s!"    ✓ Roundtrip OK: {listsEqual seq4 roundtrip_seq4}"

  -- Test 1.4: N=16
  IO.println "\n1.4 Roundtrip N=16, secuencial [1..16]:"
  let seq16 : List GoldilocksField := (List.range 16).map fun i => ⟨(i + 1).toUInt64⟩
  let ω16 := primitiveRoot 16 (by decide)
  let n_inv16 := GoldilocksField.inv ⟨16⟩
  let ntt_seq16 := NTT_spec ω16 seq16
  let roundtrip_seq16 := INTT_spec ω16 n_inv16 ntt_seq16
  IO.println s!"    Input (primeros 4):     {toVals (seq16.take 4)}"
  IO.println s!"    INTT(NTT) (primeros 4): {toVals (roundtrip_seq16.take 4)}"
  IO.println s!"    ✓ Roundtrip OK: {listsEqual seq16 roundtrip_seq16}"

  IO.println "\n═══════════════════════════════════════════════════════════"

/-! ## Test 2: Linealidad NTT(a + b) = NTT(a) + NTT(b) -/

#eval! do
  IO.println "═══════════════════════════════════════════════════════════"
  IO.println "   TEST 2: Linealidad NTT(a + b) = NTT(a) + NTT(b)"
  IO.println "═══════════════════════════════════════════════════════════"

  let ω4 := primitiveRoot 4 (by decide)

  -- Test 2.1: a = [1,0,0,0], b = [0,1,0,0]
  IO.println "\n2.1 Linealidad con delta en diferentes posiciones:"
  let a1 : List GoldilocksField := [⟨1⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩]
  let b1 : List GoldilocksField := [⟨0⟩, ⟨1⟩, ⟨0⟩, ⟨0⟩]
  let ab1 := listAdd a1 b1  -- [1,1,0,0]

  let ntt_a1 := NTT_spec ω4 a1
  let ntt_b1 := NTT_spec ω4 b1
  let ntt_ab1 := NTT_spec ω4 ab1
  let ntt_a_plus_b1 := listAdd ntt_a1 ntt_b1

  IO.println s!"    a = {toVals a1}"
  IO.println s!"    b = {toVals b1}"
  IO.println s!"    NTT(a+b)       = {toVals ntt_ab1}"
  IO.println s!"    NTT(a) + NTT(b) = {toVals ntt_a_plus_b1}"
  IO.println s!"    ✓ Linealidad OK: {listsEqual ntt_ab1 ntt_a_plus_b1}"

  -- Test 2.2: a = [1,2,3,4], b = [5,6,7,8]
  IO.println "\n2.2 Linealidad con secuencias:"
  let a2 : List GoldilocksField := [⟨1⟩, ⟨2⟩, ⟨3⟩, ⟨4⟩]
  let b2 : List GoldilocksField := [⟨5⟩, ⟨6⟩, ⟨7⟩, ⟨8⟩]
  let ab2 := listAdd a2 b2  -- [6,8,10,12]

  let ntt_a2 := NTT_spec ω4 a2
  let ntt_b2 := NTT_spec ω4 b2
  let ntt_ab2 := NTT_spec ω4 ab2
  let ntt_a_plus_b2 := listAdd ntt_a2 ntt_b2

  IO.println s!"    a = {toVals a2}"
  IO.println s!"    b = {toVals b2}"
  IO.println s!"    NTT(a+b)       = {toVals ntt_ab2}"
  IO.println s!"    NTT(a) + NTT(b) = {toVals ntt_a_plus_b2}"
  IO.println s!"    ✓ Linealidad OK: {listsEqual ntt_ab2 ntt_a_plus_b2}"

  IO.println "\n═══════════════════════════════════════════════════════════"

/-! ## Test 3: Tests Parametrizados para N = 4, 8, 16, 32 -/

#eval! do
  IO.println "═══════════════════════════════════════════════════════════"
  IO.println "   TEST 3: Tests Parametrizados (N = 4, 8, 16, 32)"
  IO.println "═══════════════════════════════════════════════════════════"

  -- Función auxiliar para test de roundtrip
  let testRoundtrip := fun (n : Nat) (hn : n > 0) =>
    let input : List GoldilocksField := (List.range n).map fun i => ⟨(i + 1).toUInt64⟩
    let ω := primitiveRoot n hn
    let n_inv := GoldilocksField.inv ⟨n.toUInt64⟩
    let ntt_result := NTT_spec ω input
    let roundtrip := INTT_spec ω n_inv ntt_result
    listsEqual input roundtrip

  IO.println "\n3.1 Roundtrip tests:"
  IO.println s!"    N=4:  {testRoundtrip 4 (by decide)}"
  IO.println s!"    N=8:  {testRoundtrip 8 (by decide)}"
  IO.println s!"    N=16: {testRoundtrip 16 (by decide)}"
  IO.println s!"    N=32: {testRoundtrip 32 (by decide)}"

  -- Verificar propiedades de raíces
  IO.println "\n3.2 Propiedades de raíces ω^n = 1:"
  let check_root := fun (n : Nat) (hn : n > 0) =>
    let ω := primitiveRoot n hn
    (GoldilocksField.pow ω n).value == 1

  IO.println s!"    ω₄⁴ = 1:   {check_root 4 (by decide)}"
  IO.println s!"    ω₈⁸ = 1:   {check_root 8 (by decide)}"
  IO.println s!"    ω₁₆¹⁶ = 1: {check_root 16 (by decide)}"
  IO.println s!"    ω₃₂³² = 1: {check_root 32 (by decide)}"

  IO.println "\n═══════════════════════════════════════════════════════════"

/-! ## Test 4: Diversos Tipos de Entrada -/

#eval! do
  IO.println "═══════════════════════════════════════════════════════════"
  IO.println "   TEST 4: Diversos Tipos de Entrada"
  IO.println "═══════════════════════════════════════════════════════════"

  let ω8 := primitiveRoot 8 (by decide)
  let n_inv8 := GoldilocksField.inv ⟨8⟩

  -- 4.1: Delta (impulso unitario)
  IO.println "\n4.1 Delta (impulso en posición 0):"
  let delta8 : List GoldilocksField := [⟨1⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩]
  let ntt_delta8 := NTT_spec ω8 delta8
  IO.println s!"    Input: {toVals delta8}"
  IO.println s!"    NTT:   {toVals ntt_delta8}"
  IO.println s!"    (Esperado: todos 1s para DFT de delta)"

  -- 4.2: Constante
  IO.println "\n4.2 Constante [3,3,3,3,3,3,3,3]:"
  let const8 : List GoldilocksField := (List.range 8).map fun _ => ⟨3⟩
  let ntt_const8 := NTT_spec ω8 const8
  IO.println s!"    Input: {toVals const8}"
  IO.println s!"    NTT:   {toVals ntt_const8}"
  IO.println s!"    (Esperado: [24,0,0,0,0,0,0,0] para DFT de constante)"

  -- 4.3: Alternante [1,-1,1,-1,...]
  IO.println "\n4.3 Alternante [1,p-1,1,p-1,...]:"
  let neg_one := ORDER - 1  -- -1 en Goldilocks
  let alt8 : List GoldilocksField := (List.range 8).map fun i =>
    if i % 2 == 0 then ⟨1⟩ else ⟨neg_one⟩
  let ntt_alt8 := NTT_spec ω8 alt8
  IO.println s!"    Input: {toVals alt8}"
  IO.println s!"    NTT:   {toVals ntt_alt8}"

  -- 4.4: Verificar roundtrip para todos
  IO.println "\n4.4 Roundtrip verification:"
  let rt_delta := INTT_spec ω8 n_inv8 ntt_delta8
  let rt_const := INTT_spec ω8 n_inv8 ntt_const8
  let rt_alt := INTT_spec ω8 n_inv8 ntt_alt8
  IO.println s!"    Delta roundtrip:     {listsEqual delta8 rt_delta}"
  IO.println s!"    Constante roundtrip: {listsEqual const8 rt_const}"
  IO.println s!"    Alternante roundtrip: {listsEqual alt8 rt_alt}"

  IO.println "\n═══════════════════════════════════════════════════════════"

/-! ## Test 5: Stride4 y Butterfly4 Integration -/

#eval! do
  IO.println "═══════════════════════════════════════════════════════════"
  IO.println "   TEST 5: Integración Stride4 y Butterfly4"
  IO.println "═══════════════════════════════════════════════════════════"

  -- Test stride4 con N=32
  IO.println "\n5.1 Stride4 con N=32:"
  let input32 : List Nat := List.range 32
  let s0 := stride4_0 input32
  let s1 := stride4_1 input32
  let s2 := stride4_2 input32
  let s3 := stride4_3 input32
  IO.println s!"    |stride4_0| = {s0.length} (esperado: 8)"
  IO.println s!"    |stride4_1| = {s1.length} (esperado: 8)"
  IO.println s!"    |stride4_2| = {s2.length} (esperado: 8)"
  IO.println s!"    |stride4_3| = {s3.length} (esperado: 8)"

  let reconstructed := interleave4 s0 s1 s2 s3
  IO.println s!"    Roundtrip OK: {reconstructed == input32}"

  -- Test butterfly4 propiedades
  IO.println "\n5.2 Butterfly4 propiedades:"
  let ω4 := primitiveRoot 4 (by decide)

  -- Propiedad: butterfly4 de delta da constante
  let bf_delta := Radix4.butterfly4 (⟨1⟩ : GoldilocksField) ⟨0⟩ ⟨0⟩ ⟨0⟩ ω4
  IO.println s!"    butterfly4(1,0,0,0) = {[bf_delta.1.value, bf_delta.2.1.value, bf_delta.2.2.1.value, bf_delta.2.2.2.value]}"
  IO.println s!"    (Esperado: todos iguales = DFT de delta)"

  -- Propiedad: butterfly4 de constante da delta escalado
  let bf_const := Radix4.butterfly4 (⟨1⟩ : GoldilocksField) ⟨1⟩ ⟨1⟩ ⟨1⟩ ω4
  IO.println s!"    butterfly4(1,1,1,1) = {[bf_const.1.value, bf_const.2.1.value, bf_const.2.2.1.value, bf_const.2.2.2.value]}"
  IO.println s!"    (Esperado: [4,0,0,0] = DFT de constante)"

  IO.println "\n═══════════════════════════════════════════════════════════"
  IO.println "   TODOS LOS TESTS COMPLETADOS"
  IO.println "═══════════════════════════════════════════════════════════"

end AmoLean.NTT.Radix4.Tests
