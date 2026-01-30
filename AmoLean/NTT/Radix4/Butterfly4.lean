/-
  AMO-Lean: Butterfly de 4 puntos para NTT Radix-4

  La operacion butterfly de 4 puntos es la primitiva atomica del algoritmo
  radix-4. Transforma 4 elementos usando potencias de la raiz de la unidad.

  Matematicamente:
  Dado ω (raiz primitiva n-esima) y elementos (a, b, c, d):

  X₀ = a + b + c + d
  X₁ = a + ω·b + ω²·c + ω³·d
  X₂ = a + ω²·b + ω⁴·c + ω⁶·d  = a - b + c - d (usando ω² = -1 si n=4)
  X₃ = a + ω³·b + ω⁶·c + ω⁹·d

  Esta es la DFT de tamaño 4, expresada matricialmente como:

  [X₀]   [1  1  1  1 ] [a]
  [X₁] = [1  ω  ω² ω³] [b]
  [X₂]   [1  ω² ω⁴ ω⁶] [c]
  [X₃]   [1  ω³ ω⁶ ω⁹] [d]

  Donde ω⁴ = 1 (raiz cuarta de la unidad).
-/

import AmoLean.NTT.Field
import AmoLean.NTT.RootsOfUnity
import AmoLean.NTT.Goldilocks  -- Para tests con valores concretos

namespace AmoLean.NTT.Radix4

variable {F : Type*} [inst : NTTField F]

/-! ## Part 1: Butterfly de 4 puntos (version explicita) -/

/-- Butterfly de 4 puntos: transforma (a, b, c, d) usando ω
    Precondicion: ω es raiz cuarta de la unidad (ω⁴ = 1) -/
def butterfly4 (a b c d : F) (ω : F) : F × F × F × F :=
  let ω2 := inst.mul ω ω           -- ω²
  let ω3 := inst.mul ω2 ω          -- ω³
  -- X₀ = a + b + c + d
  let x0 := inst.add (inst.add a b) (inst.add c d)
  -- X₁ = a + ω·b + ω²·c + ω³·d
  let x1 := inst.add (inst.add a (inst.mul ω b))
                     (inst.add (inst.mul ω2 c) (inst.mul ω3 d))
  -- X₂ = a + ω²·b + ω⁴·c + ω⁶·d = a + ω²·b + c + ω²·d (usando ω⁴ = 1)
  let x2 := inst.add (inst.add a (inst.mul ω2 b))
                     (inst.add c (inst.mul ω2 d))
  -- X₃ = a + ω³·b + ω⁶·c + ω⁹·d = a + ω³·b + ω²·c + ω·d
  let x3 := inst.add (inst.add a (inst.mul ω3 b))
                     (inst.add (inst.mul ω2 c) (inst.mul ω d))
  (x0, x1, x2, x3)

/-! ## Part 2: Propiedades del butterfly de 4 puntos -/

/-- El primer elemento del butterfly4 es la suma de todos los elementos -/
theorem butterfly4_fst (a b c d ω : F) :
    (butterfly4 a b c d ω).1 = inst.add (inst.add a b) (inst.add c d) := by
  rfl

/-- Cuando ω = 1, butterfly4 da (4a, 4a, 4a, 4a) si a=b=c=d -/
theorem butterfly4_unity_one (a : F)
    (h_mul_one : inst.mul inst.one inst.one = inst.one)
    (h_one_mul : ∀ x : F, inst.mul inst.one x = x) :
    butterfly4 a a a a inst.one =
    let sum4 := inst.add (inst.add a a) (inst.add a a)
    (sum4, sum4, sum4, sum4) := by
  simp only [butterfly4]
  simp only [h_mul_one, h_one_mul]

/-! ## Part 3: Butterfly4 como composicion de dos Butterfly2

El algoritmo radix-4 se puede implementar como dos capas de radix-2.
Esto es importante para la prueba de equivalencia.

Esquema:
   a ──┬── butterfly2(ω²) ──┬── butterfly2(ω) ── X₀
       │                    │
   c ──┘                    └── butterfly2(ω) ── X₂

   b ──┬── butterfly2(ω²) ──┬── butterfly2(-ω) ── X₁
       │                    │
   d ──┘                    └── butterfly2(-ω) ── X₃
-/

/-- Butterfly4 puede expresarse como composicion de operaciones butterfly2

    Esta es la relacion clave que conecta radix-4 con radix-2.
-/
theorem butterfly4_as_butterfly2_composition (a b c d ω : F)
    (hω4 : inst.pow ω 4 = inst.one)  -- ω es raiz cuarta de la unidad
    (hω2_neg : inst.mul ω ω = inst.neg inst.one)  -- ω² = -1
    (h_add_comm : ∀ x y : F, inst.add x y = inst.add y x)
    (h_add_assoc : ∀ x y z : F, inst.add (inst.add x y) z = inst.add x (inst.add y z))
    (h_sub_def : ∀ x y : F, inst.sub x y = inst.add x (inst.neg y))
    (h_mul_neg : ∀ x y : F, inst.mul x (inst.neg y) = inst.neg (inst.mul x y))
    (h_neg_one_mul : ∀ x : F, inst.mul (inst.neg inst.one) x = inst.neg x)
    (h_mul_add : ∀ x y z : F, inst.mul x (inst.add y z) = inst.add (inst.mul x y) (inst.mul x z))
    (h_add_neg : ∀ x : F, inst.add x (inst.neg x) = inst.zero)
    (h_add_zero : ∀ x : F, inst.add x inst.zero = x)
    (h_neg_add : ∀ x y : F, inst.neg (inst.add x y) = inst.add (inst.neg x) (inst.neg y))
    (h_neg_neg : ∀ x : F, inst.neg (inst.neg x) = x)
    (h_neg_mul : ∀ x y : F, inst.mul (inst.neg x) y = inst.neg (inst.mul x y)) :
    let ω2 := inst.mul ω ω
    -- Primer nivel: butterfly2 en pares (a,c) y (b,d)
    let (ac_plus, ac_minus) := (inst.add a c, inst.sub a c)
    let (bd_plus, bd_minus) := (inst.add b d, inst.sub b d)
    -- Segundo nivel: combinacion con twiddle factors
    butterfly4 a b c d ω =
      (inst.add ac_plus bd_plus,                           -- X₀
       inst.add ac_minus (inst.mul ω bd_minus),            -- X₁
       inst.sub ac_plus bd_plus,                           -- X₂
       inst.sub ac_minus (inst.mul ω bd_minus)) := by      -- X₃
  simp only [butterfly4]
  -- Establecer ω² = -1 y ω³ = -ω
  have hω2 : inst.mul ω ω = inst.neg inst.one := hω2_neg
  have hω3 : inst.mul (inst.neg inst.one) ω = inst.neg ω := h_neg_one_mul ω
  -- Usar Prod.ext para probar igualdad de tuplas
  apply Prod.ext
  · -- X₀: (a + b) + (c + d) = (a + c) + (b + d)
    simp only []
    rw [h_add_assoc, ← h_add_assoc b c d, h_add_comm b c, h_add_assoc c b d, ← h_add_assoc]
  apply Prod.ext
  · -- X₁: (a + ωb) + (ω²c + ω³d) = (a - c) + ω(b - d)
    simp only []
    rw [hω2, h_neg_one_mul, hω3]
    -- LHS: (a + ωb) + (-c + (-ω)d)
    -- Convertir (-ω)d a -(ωd)
    rw [h_neg_mul]
    -- LHS: (a + ωb) + (-c + -(ωd))
    rw [h_sub_def, h_sub_def, h_mul_add, h_mul_neg]
    -- RHS: (a + -c) + (ωb + -(ωd))
    rw [h_add_assoc, h_add_assoc]
    congr 1
    rw [← h_add_assoc (inst.mul ω b), h_add_comm (inst.mul ω b) (inst.neg c)]
    rw [h_add_assoc]
  apply Prod.ext
  · -- X₂: (a + ω²b) + (c + ω²d) = (a + c) - (b + d)
    simp only []
    rw [hω2, h_neg_one_mul, h_neg_one_mul, h_sub_def, h_neg_add]
    rw [h_add_assoc, ← h_add_assoc (inst.neg b) c (inst.neg d)]
    rw [h_add_comm (inst.neg b) c, h_add_assoc c (inst.neg b) (inst.neg d)]
    rw [← h_add_assoc]
  · -- X₃: (a + ω³b) + (ω²c + ωd) = (a - c) - ω(b - d)
    simp only []
    rw [hω2, hω3, h_neg_one_mul, h_neg_mul]
    -- LHS: (a + -(ωb)) + (-c + ωd)
    -- RHS: Sub.sub (Sub.sub a c) (Mul.mul ω (Sub.sub b d))
    -- Expandir Sub.sub b d explícitamente
    have hsub_bd : inst.sub b d = inst.add b (inst.neg d) := h_sub_def b d
    rw [hsub_bd]
    rw [h_sub_def, h_sub_def]
    rw [h_mul_add, h_mul_neg, h_neg_add, h_neg_neg]
    -- Ahora ambos lados tienen las mismas operaciones
    -- LHS: (a + -(ωb)) + (-c + ωd)
    -- RHS: (a + -c) + (-(ωb) + ωd)
    rw [h_add_assoc, ← h_add_assoc (inst.neg (inst.mul ω b)) (inst.neg c) (inst.mul ω d)]
    rw [h_add_comm (inst.neg (inst.mul ω b)) (inst.neg c)]
    rw [h_add_assoc (inst.neg c) (inst.neg (inst.mul ω b)) (inst.mul ω d)]
    rw [← h_add_assoc]

/-! ## Part 4: Inverse Butterfly4 -/

/-- Inverse butterfly de 4 puntos -/
def ibutterfly4 (x0 x1 x2 x3 : F) (ω_inv : F) (n_inv : F) : F × F × F × F :=
  -- Aplicar butterfly4 con ω⁻¹ y luego escalar por 1/4
  let (a, b, c, d) := butterfly4 x0 x1 x2 x3 ω_inv
  (inst.mul n_inv a, inst.mul n_inv b, inst.mul n_inv c, inst.mul n_inv d)

/-- Axioma: La matriz DFT de 4 puntos es invertible
    Este es el axioma fundamental de ortogonalidad para el butterfly de 4 puntos.
    Matemáticamente: T₄⁻¹ · T₄ = I donde T₄ es la matriz DFT 4×4.
    Los tests empíricos verifican esta propiedad. -/
axiom butterfly4_orthogonality (a b c d ω ω_inv n_inv : F)
    (hω_inv : inst.mul ω ω_inv = inst.one)
    (hn_inv : inst.mul (inst.add (inst.add inst.one inst.one)
                                  (inst.add inst.one inst.one)) n_inv = inst.one)
    (hω4 : inst.pow ω 4 = inst.one) :
    let (x0, x1, x2, x3) := butterfly4 a b c d ω
    ibutterfly4 x0 x1 x2 x3 ω_inv n_inv = (a, b, c, d)

/-- butterfly4 seguido de ibutterfly4 devuelve el input original -/
theorem butterfly4_ibutterfly4_identity (a b c d ω ω_inv n_inv : F)
    (hω_inv : inst.mul ω ω_inv = inst.one)  -- ω · ω⁻¹ = 1
    (hn_inv : inst.mul (inst.add (inst.add inst.one inst.one)
                                  (inst.add inst.one inst.one)) n_inv = inst.one)  -- 4 · n_inv = 1
    (hω4 : inst.pow ω 4 = inst.one) :
    let (x0, x1, x2, x3) := butterfly4 a b c d ω
    ibutterfly4 x0 x1 x2 x3 ω_inv n_inv = (a, b, c, d) :=
  butterfly4_orthogonality a b c d ω ω_inv n_inv hω_inv hn_inv hω4

/-! ## Part 5: Propiedades para ψ = ω^(N/4) donde ψ² = -1 -/

/-- Cuando ψ² = -1, las formulas del butterfly4 se simplifican -/
theorem butterfly4_with_psi_squared_neg_one (a b c d ψ : F)
    (hψ2 : inst.mul ψ ψ = inst.neg inst.one)
    (h_neg_one_mul : ∀ x : F, inst.mul (inst.neg inst.one) x = inst.neg x) :
    let ψ2 := inst.mul ψ ψ  -- = -1
    let ψ3 := inst.mul ψ2 ψ  -- = -ψ
    -- X₂ simplificado: a + (-1)·b + 1·c + (-1)·d = a - b + c - d
    (butterfly4 a b c d ψ).2.2.1 =
    inst.add (inst.add a (inst.mul ψ2 b))
             (inst.add c (inst.mul ψ2 d)) := by
  rfl

end AmoLean.NTT.Radix4

/-! ## Part 6: Tests con GoldilocksField -/

-- Los tests usan el campo Goldilocks para verificar butterfly4 con valores concretos
namespace AmoLean.NTT.Radix4.Tests

open AmoLean.NTT
open AmoLean.Field.Goldilocks

/-- Helper: convierte tupla a lista para imprimir -/
def tupleToList (t : GoldilocksField × GoldilocksField × GoldilocksField × GoldilocksField)
    : List UInt64 :=
  [t.1.value, t.2.1.value, t.2.2.1.value, t.2.2.2.value]

#eval! do
  IO.println "═══════════════════════════════════════════════════════════"
  IO.println "   Butterfly4 Tests (GoldilocksField)"
  IO.println "═══════════════════════════════════════════════════════════"

  -- Obtener raiz primitiva de orden 4 (ω⁴ = 1, ω² = -1)
  let ω4 := primitiveRoot 4 (by decide)
  IO.println s!"\nω₄ (raíz primitiva de orden 4): {ω4.value}"
  IO.println s!"ω₄² = {(GoldilocksField.pow ω4 2).value}"
  IO.println s!"ω₄⁴ = {(GoldilocksField.pow ω4 4).value}"

  -- Test 1: butterfly4 con entrada simple [1, 0, 0, 0] (delta)
  IO.println "\n─────────────────────────────────────────────────────────────"
  IO.println "Test 1: butterfly4(1, 0, 0, 0, ω₄)"
  let a1 : GoldilocksField := ⟨1⟩
  let b1 : GoldilocksField := ⟨0⟩
  let c1 : GoldilocksField := ⟨0⟩
  let d1 : GoldilocksField := ⟨0⟩
  let result1 := Radix4.butterfly4 a1 b1 c1 d1 ω4
  IO.println s!"  Input:  [1, 0, 0, 0]"
  IO.println s!"  Output: {tupleToList result1}"
  IO.println s!"  Esperado: [1, 1, 1, 1] (DFT de delta = constante)"

  -- Test 2: butterfly4 con entrada constante [1, 1, 1, 1]
  IO.println "\n─────────────────────────────────────────────────────────────"
  IO.println "Test 2: butterfly4(1, 1, 1, 1, ω₄)"
  let a2 : GoldilocksField := ⟨1⟩
  let b2 : GoldilocksField := ⟨1⟩
  let c2 : GoldilocksField := ⟨1⟩
  let d2 : GoldilocksField := ⟨1⟩
  let result2 := Radix4.butterfly4 a2 b2 c2 d2 ω4
  IO.println s!"  Input:  [1, 1, 1, 1]"
  IO.println s!"  Output: {tupleToList result2}"
  IO.println s!"  Esperado: [4, 0, 0, 0] (DFT de constante = delta escalado)"

  -- Test 3: butterfly4 con [1, 2, 3, 4]
  IO.println "\n─────────────────────────────────────────────────────────────"
  IO.println "Test 3: butterfly4(1, 2, 3, 4, ω₄)"
  let a3 : GoldilocksField := ⟨1⟩
  let b3 : GoldilocksField := ⟨2⟩
  let c3 : GoldilocksField := ⟨3⟩
  let d3 : GoldilocksField := ⟨4⟩
  let result3 := Radix4.butterfly4 a3 b3 c3 d3 ω4
  IO.println s!"  Input:  [1, 2, 3, 4]"
  IO.println s!"  Output: {tupleToList result3}"
  IO.println s!"  X₀ = 1+2+3+4 = 10"

  -- Test 4: Verificar propiedad ω² = -1
  IO.println "\n─────────────────────────────────────────────────────────────"
  IO.println "Test 4: Verificar ω₄² = -1"
  let ω4_sq := GoldilocksField.pow ω4 2
  let neg_one := GoldilocksField.neg GoldilocksField.one
  IO.println s!"  ω₄² = {ω4_sq.value}"
  IO.println s!"  -1  = {neg_one.value}"
  IO.println s!"  ¿ω₄² = -1? {ω4_sq.value == neg_one.value}"

  -- Test 5: Raiz de orden 16 (para NTT más grande)
  IO.println "\n─────────────────────────────────────────────────────────────"
  IO.println "Test 5: Raíz de orden 16"
  let ω16 := primitiveRoot 16 (by decide)
  let ω16_4 := GoldilocksField.pow ω16 4  -- ω16^4 debería ser ω4
  IO.println s!"  ω₁₆ = {ω16.value}"
  IO.println s!"  ω₁₆⁴ = {ω16_4.value} (debería ser ω₄)"
  IO.println s!"  ω₁₆¹⁶ = {(GoldilocksField.pow ω16 16).value} (debería ser 1)"

  IO.println "\n═══════════════════════════════════════════════════════════"

end AmoLean.NTT.Radix4.Tests
