/-
  AMO-Lean: Funciones de Stride-4 para NTT Radix-4

  El algoritmo radix-4 divide el problema de tamaño N en 4 subproblemas
  de tamaño N/4. Para esto necesitamos extraer elementos en posiciones
  con diferentes residuos modulo 4.

  stride4_0: elementos en posiciones 0, 4, 8, 12, ...  (i % 4 = 0)
  stride4_1: elementos en posiciones 1, 5, 9, 13, ...  (i % 4 = 1)
  stride4_2: elementos en posiciones 2, 6, 10, 14, ... (i % 4 = 2)
  stride4_3: elementos en posiciones 3, 7, 11, 15, ... (i % 4 = 3)

  Decisión de diseño (2026-01-30):
  Usamos pattern matching en lugar de filterMap+enum para permitir
  inducción estructural limpia con .induct, siguiendo el patrón
  de evens/odds en ListUtils.lean.
-/

import AmoLean.NTT.ListUtils

namespace AmoLean.NTT.Radix4

/-! ## Part 1: Definiciones de stride4 con pattern matching -/

/-- Extrae elementos en posiciones 0, 4, 8, ... (residuo 0 mod 4) -/
def stride4_0 : List α → List α
  | [] => []
  | [x] => [x]
  | [x, _] => [x]
  | [x, _, _] => [x]
  | x :: _ :: _ :: _ :: xs => x :: stride4_0 xs

/-- Extrae elementos en posiciones 1, 5, 9, ... (residuo 1 mod 4) -/
def stride4_1 : List α → List α
  | [] => []
  | [_] => []
  | [_, y] => [y]
  | [_, y, _] => [y]
  | _ :: y :: _ :: _ :: xs => y :: stride4_1 xs

/-- Extrae elementos en posiciones 2, 6, 10, ... (residuo 2 mod 4) -/
def stride4_2 : List α → List α
  | [] => []
  | [_] => []
  | [_, _] => []
  | [_, _, z] => [z]
  | _ :: _ :: z :: _ :: xs => z :: stride4_2 xs

/-- Extrae elementos en posiciones 3, 7, 11, ... (residuo 3 mod 4) -/
def stride4_3 : List α → List α
  | [] => []
  | [_] => []
  | [_, _] => []
  | [_, _, _] => []
  | _ :: _ :: _ :: w :: xs => w :: stride4_3 xs

/-! ## Part 2: Propiedades basicas -/

@[simp] theorem stride4_0_nil : stride4_0 ([] : List α) = [] := rfl
@[simp] theorem stride4_1_nil : stride4_1 ([] : List α) = [] := rfl
@[simp] theorem stride4_2_nil : stride4_2 ([] : List α) = [] := rfl
@[simp] theorem stride4_3_nil : stride4_3 ([] : List α) = [] := rfl

/-- stride4_0 de un singleton es el singleton -/
@[simp] theorem stride4_0_singleton (x : α) : stride4_0 [x] = [x] := rfl

/-- stride4_1, stride4_2, stride4_3 de singleton son vacios -/
@[simp] theorem stride4_1_singleton (x : α) : stride4_1 [x] = [] := rfl
@[simp] theorem stride4_2_singleton (x : α) : stride4_2 [x] = [] := rfl
@[simp] theorem stride4_3_singleton (x : α) : stride4_3 [x] = [] := rfl

/-! ## Part 3: Propiedades de longitud -/

/-- Longitud de stride4_0 -/
theorem stride4_0_length (l : List α) :
    (stride4_0 l).length = (l.length + 3) / 4 := by
  induction l using stride4_0.induct with
  | case1 => simp [stride4_0]
  | case2 x => simp [stride4_0]
  | case3 x y => simp [stride4_0]
  | case4 x y z => simp [stride4_0]
  | case5 x y z w xs ih =>
    simp only [stride4_0, List.length_cons]
    rw [ih]
    omega

/-- Longitud de stride4_1 -/
theorem stride4_1_length (l : List α) :
    (stride4_1 l).length = (l.length + 2) / 4 := by
  induction l using stride4_1.induct with
  | case1 => simp [stride4_1]
  | case2 x => simp [stride4_1]
  | case3 x y => simp [stride4_1]
  | case4 x y z => simp [stride4_1]
  | case5 x y z w xs ih =>
    simp only [stride4_1, List.length_cons]
    rw [ih]
    omega

/-- Longitud de stride4_2 -/
theorem stride4_2_length (l : List α) :
    (stride4_2 l).length = (l.length + 1) / 4 := by
  induction l using stride4_2.induct with
  | case1 => simp [stride4_2]
  | case2 x => simp [stride4_2]
  | case3 x y => simp [stride4_2]
  | case4 x y z => simp [stride4_2]
  | case5 x y z w xs ih =>
    simp only [stride4_2, List.length_cons]
    rw [ih]
    omega

/-- Longitud de stride4_3 -/
theorem stride4_3_length (l : List α) :
    (stride4_3 l).length = l.length / 4 := by
  induction l using stride4_3.induct with
  | case1 => simp [stride4_3]
  | case2 x => simp [stride4_3]
  | case3 x y => simp [stride4_3]
  | case4 x y z => simp [stride4_3]
  | case5 x y z w xs ih =>
    simp only [stride4_3, List.length_cons]
    rw [ih]
    omega

/-- Teorema principal: cuando 4 | length, cada stride tiene length/4 elementos -/
theorem stride4_lengths (xs : List α) (h : xs.length % 4 = 0) :
    (stride4_0 xs).length = xs.length / 4 ∧
    (stride4_1 xs).length = xs.length / 4 ∧
    (stride4_2 xs).length = xs.length / 4 ∧
    (stride4_3 xs).length = xs.length / 4 := by
  rw [stride4_0_length, stride4_1_length, stride4_2_length, stride4_3_length]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

/-! ## Part 4: Suma de longitudes -/

/-- Las 4 partes suman la longitud original -/
theorem stride4_total_length (l : List α) :
    (stride4_0 l).length + (stride4_1 l).length +
    (stride4_2 l).length + (stride4_3 l).length = l.length := by
  rw [stride4_0_length, stride4_1_length, stride4_2_length, stride4_3_length]
  omega

/-! ## Part 5: Interleave de 4 listas -/

/-- Intercala 4 listas: [a,b,c,d], [e,f,g,h], [i,j,k,l], [m,n,o,p]
    -> [a,e,i,m, b,f,j,n, c,g,k,o, d,h,l,p] -/
def interleave4 : List α → List α → List α → List α → List α
  | [], [], [], [] => []
  | [], ys, zs, ws => ys ++ zs ++ ws  -- Caso residual
  | xs, [], zs, ws => xs ++ zs ++ ws
  | xs, ys, [], ws => xs ++ ys ++ ws
  | xs, ys, zs, [] => xs ++ ys ++ zs
  | x :: xs, y :: ys, z :: zs, w :: ws => x :: y :: z :: w :: interleave4 xs ys zs ws

/-- Longitud del interleave4 cuando las listas tienen igual longitud -/
theorem interleave4_length (xs ys zs ws : List α)
    (h1 : xs.length = ys.length) (h2 : ys.length = zs.length) (h3 : zs.length = ws.length) :
    (interleave4 xs ys zs ws).length = 4 * xs.length := by
  induction xs, ys, zs, ws using interleave4.induct with
  | case1 => simp [interleave4]
  | case2 ys zs ws =>
    -- xs = [], h1: 0 = ys.length, así que ys = []
    simp only [List.length_nil] at h1
    simp only [← h1, ← h2, ← h3, interleave4, List.length_append, List.length_nil]
  | case3 xs zs ws =>
    -- ys = [], h1: xs.length = 0, así que xs = []
    simp only [List.length_nil] at h1
    simp only [h1, ← h2, ← h3, interleave4, List.length_append, List.length_nil]
  | case4 xs ys ws =>
    -- zs = [], xs ≠ [], ys ≠ [], h2: ys.length = 0 → contradicción
    simp only [List.length_nil] at h2
    -- h2: ys.length = 0, pero el patrón dice ys ≠ []
    -- Usamos omega para derivar contradicción: h1: xs.length = ys.length = 0, pero xs ≠ []
    simp only [h2] at h1
    simp only [h1, h2, ← h3, interleave4, List.length_append, List.length_nil]
  | case5 xs ys zs =>
    -- ws = [], xs ≠ [], ys ≠ [], zs ≠ [], h3: zs.length = 0 → contradicción
    simp only [List.length_nil] at h3
    simp only [h3] at h2
    simp only [h2] at h1
    simp only [h1, h2, h3, interleave4, List.length_append, List.length_nil]
  | case6 x xs y ys z zs w ws ih =>
    simp only [interleave4, List.length_cons] at h1 h2 h3 ⊢
    have h1' : xs.length = ys.length := by omega
    have h2' : ys.length = zs.length := by omega
    have h3' : zs.length = ws.length := by omega
    rw [ih h1' h2' h3']
    omega

/-! ## Part 6: Roundtrip property -/

/-- Intercalar los 4 strides reconstruye la lista original -/
theorem interleave4_stride4 (xs : List α) (h : xs.length % 4 = 0) :
    interleave4 (stride4_0 xs) (stride4_1 xs) (stride4_2 xs) (stride4_3 xs) = xs := by
  induction xs using stride4_0.induct with
  | case1 => rfl
  | case2 x => simp [stride4_0, stride4_1, stride4_2, stride4_3, interleave4] at h ⊢
  | case3 x y => simp [stride4_0, stride4_1, stride4_2, stride4_3] at h
  | case4 x y z => simp [stride4_0, stride4_1, stride4_2, stride4_3] at h
  | case5 x y z w xs ih =>
    simp only [stride4_0, stride4_1, stride4_2, stride4_3, interleave4]
    simp only [List.length_cons] at h
    have h' : xs.length % 4 = 0 := by omega
    rw [ih h']

/-! ## Part 7: Relacion con evens/odds -/

/-- stride4_0 ∪ stride4_2 = evens (elementos en posiciones pares)
    Nota: requiere interleave apropiado -/
theorem stride4_evens_relation (xs : List α) (h : xs.length % 4 = 0) :
    AmoLean.NTT.interleave (stride4_0 xs) (stride4_2 xs) = AmoLean.NTT.evens xs := by
  induction xs using stride4_0.induct with
  | case1 => rfl
  | case2 x => simp [stride4_0, stride4_2, AmoLean.NTT.interleave, AmoLean.NTT.evens] at h ⊢
  | case3 x y => simp [stride4_0] at h
  | case4 x y z => simp [stride4_0] at h
  | case5 x y z w xs ih =>
    simp only [stride4_0, stride4_2, AmoLean.NTT.interleave, AmoLean.NTT.evens]
    simp only [List.length_cons] at h
    have h' : xs.length % 4 = 0 := by omega
    rw [ih h']

/-- stride4_1 ∪ stride4_3 = odds (elementos en posiciones impares) -/
theorem stride4_odds_relation (xs : List α) (h : xs.length % 4 = 0) :
    AmoLean.NTT.interleave (stride4_1 xs) (stride4_3 xs) = AmoLean.NTT.odds xs := by
  induction xs using stride4_1.induct with
  | case1 => rfl
  | case2 x => simp [stride4_1, stride4_3, AmoLean.NTT.interleave, AmoLean.NTT.odds] at h ⊢
  | case3 x y => simp [stride4_1] at h
  | case4 x y z => simp [stride4_1] at h
  | case5 x y z w xs ih =>
    simp only [stride4_1, stride4_3, AmoLean.NTT.interleave, AmoLean.NTT.odds]
    simp only [List.length_cons] at h
    have h' : xs.length % 4 = 0 := by omega
    rw [ih h']

/-! ## Part 8: Tests -/

#eval! do
  IO.println "═══════════════════════════════════════════════════════════"
  IO.println "   Stride4 Tests"
  IO.println "═══════════════════════════════════════════════════════════"

  let test := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
  IO.println s!"\nOriginal (N=16): {test}"
  IO.println s!"stride4_0: {stride4_0 test}"  -- [0, 4, 8, 12]
  IO.println s!"stride4_1: {stride4_1 test}"  -- [1, 5, 9, 13]
  IO.println s!"stride4_2: {stride4_2 test}"  -- [2, 6, 10, 14]
  IO.println s!"stride4_3: {stride4_3 test}"  -- [3, 7, 11, 15]

  let reconstructed := interleave4 (stride4_0 test) (stride4_1 test)
                                   (stride4_2 test) (stride4_3 test)
  IO.println s!"\nReconstruido: {reconstructed}"
  IO.println s!"Roundtrip OK: {reconstructed == test}"

  -- Test longitudes
  IO.println s!"\nLongitudes:"
  IO.println s!"  stride4_0: {(stride4_0 test).length} (esperado: 4)"
  IO.println s!"  stride4_1: {(stride4_1 test).length} (esperado: 4)"
  IO.println s!"  stride4_2: {(stride4_2 test).length} (esperado: 4)"
  IO.println s!"  stride4_3: {(stride4_3 test).length} (esperado: 4)"

  IO.println "\n═══════════════════════════════════════════════════════════"

end AmoLean.NTT.Radix4
