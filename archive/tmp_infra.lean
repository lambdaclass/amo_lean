/-- Shifted foldl write: writing at base+j via enumFrom(n) = writing via enumFrom(base+n). -/
private theorem foldl_write_shifted [Inhabited α]
    (vals : List α) (wm : Memory α) (base n : Nat) :
    (vals.enumFrom n).foldl (fun acc x => acc.write (base + x.1) x.2) wm =
    (vals.enumFrom (base + n)).foldl (fun acc x => acc.write x.1 x.2) wm := by
  induction vals generalizing wm n with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.enumFrom_cons, List.foldl_cons]
    exact ih (wm.write (base + n) hd) (n + 1)

/-- evalScatter for Scatter.block m₂ v at iteration i is foldl write at enumFrom(i*m₂). -/
private theorem evalScatter_block_eq_enumFrom [Inhabited α]
    (v : LoopVar) (m₂ i : Nat) (wm : Memory α) (vals : List α) :
    evalScatter (LoopEnv.empty.bind v i) (Scatter.block m₂ v) wm vals =
    (vals.enumFrom (i * m₂)).foldl (fun acc x => acc.write x.1 x.2) wm := by
  simp only [evalScatter, Scatter.block, evalIdxExpr_affine_bind, List.enum,
             Nat.zero_add, Nat.one_mul]
  have h := foldl_write_shifted vals wm (m₂ * i) 0
  simp only [Nat.add_zero] at h
  rw [h, Nat.mul_comm]

/-- Length of flatMap over range when each component has fixed length. -/
private theorem flatMap_range_length (vals : Nat → List α) (m₂ i : Nat)
    (hlen : ∀ j, j < i → (vals j).length = m₂) :
    ((List.range i).flatMap vals).length = i * m₂ := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [List.range_succ, List.flatMap_append, List.length_append,
        List.flatMap_cons, List.flatMap_nil, List.append_nil,
        ih (fun j hj => hlen j (by omega)), hlen i (by omega)]
    ring

/-- Size of memory after foldl write with enumFrom is preserved when writes are in bounds. -/
private theorem foldl_write_enumFrom_preserves_size [Inhabited α]
    (vals : List α) (wm : Memory α) (k : Nat)
    (hk : k + vals.length ≤ wm.size) :
    ((vals.enumFrom k).foldl (fun acc x => acc.write x.1 x.2) wm).size = wm.size := by
  induction vals generalizing wm k with
  | nil => simp [List.enumFrom, List.foldl_nil]
  | cons hd tl ih =>
    simp only [List.enumFrom_cons, List.foldl_cons, List.length_cons] at hk ⊢
    have hk_lt : k < wm.size := by omega
    have hsize' : (wm.write k hd).size = wm.size := Memory.size_write_eq wm k hd hk_lt
    rw [ih (wm.write k hd) (k + 1) (by rw [hsize']; omega)]
    exact hsize'

/-- Block scatter loop invariant: after i iterations, the toList telescopes.
    The final toList = concat(vals₀, ..., vals_{i-1}) ++ initial.drop(i*m₂).
    After m₁ iterations, drop(m₁*m₂) = [], so the result is independent of initial wm. -/
private theorem block_scatter_loop_inv [Inhabited α]
    (m₁ m₂ : Nat) (wm : Memory α) (vals : Nat → List α)
    (hlen : ∀ j, j < m₁ → (vals j).length = m₂)
    (hwm : wm.size = m₁ * m₂) (i : Nat) (hi : i ≤ m₁) :
    let wm_i := (List.range i).foldl (fun wm' j =>
      ((vals j).enumFrom (j * m₂)).foldl (fun acc x => acc.write x.1 x.2) wm') wm
    wm_i.toList = (List.range i).flatMap vals ++ wm.toList.drop (i * m₂)
    ∧ wm_i.size = m₁ * m₂ := by
  induction i with
  | zero =>
    simp only [List.range_zero, List.foldl_nil, List.flatMap_nil, Nat.zero_mul,
               List.drop_zero, List.nil_append]
    exact ⟨rfl, hwm⟩
  | succ i ih =>
    have hi' : i ≤ m₁ := by omega
    obtain ⟨ih_toList, ih_size⟩ := ih hi'
    simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    set wm_i := (List.range i).foldl (fun wm' j =>
      ((vals j).enumFrom (j * m₂)).foldl (fun acc x => acc.write x.1 x.2) wm') wm
    have hvals_len : (vals i).length = m₂ := hlen i (by omega)
    have h_bound : i * m₂ + (vals i).length ≤ wm_i.size := by
      rw [hvals_len, ih_size]; nlinarith [hi]
    have h_scatter := scatter_enumFrom_general (vals i) wm_i (i * m₂) h_bound
    have hfm_len : ((List.range i).flatMap vals).length = i * m₂ :=
      flatMap_range_length vals m₂ i (fun j hj => hlen j (by omega))
    constructor
    · -- toList telescopes: apply scatter_enumFrom_general then simplify take/drop
      rw [h_scatter, ih_toList, hvals_len]
      -- Simplify take: (fm ++ ds).take(i*m₂) = fm when fm.length = i*m₂
      have htake : ((List.range i).flatMap vals ++ wm.toList.drop (i * m₂)).take (i * m₂)
                 = (List.range i).flatMap vals := by
        rw [← hfm_len]; exact List.take_left ..
      -- Simplify drop: (fm ++ ds).drop(i*m₂ + m₂) = wm.drop((i+1)*m₂)
      have hdrop : ((List.range i).flatMap vals ++ wm.toList.drop (i * m₂)).drop (i * m₂ + m₂)
                 = wm.toList.drop ((i + 1) * m₂) := by
        rw [← hfm_len, ← List.drop_drop]
        rw [List.drop_left, List.drop_drop]
        ring_nf
      rw [htake, hdrop]
      -- flatMap(0..i) = flatMap(0..i-1) ++ vals i
      rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
          List.append_nil, List.append_assoc]
    · -- Size preservation
      rw [foldl_write_enumFrom_preserves_size (vals i) wm_i (i * m₂) h_bound]
      exact ih_size

/-- WriteMem irrelevance for block scatter loops.
    After m₁ iterations of block scatter (each writing m₂ values), the result
    is independent of the initial writeMem when wm.size = m₁ * m₂. -/
private theorem block_scatter_loop_wm_irrelevant [Inhabited α]
    (m₁ m₂ : Nat) (wm1 wm2 : Memory α) (vals : Nat → List α)
    (hlen : ∀ j, j < m₁ → (vals j).length = m₂)
    (hwm1 : wm1.size = m₁ * m₂) (hwm2 : wm2.size = m₁ * m₂) :
    (List.range m₁).foldl (fun wm' j =>
      ((vals j).enumFrom (j * m₂)).foldl (fun acc x => acc.write x.1 x.2) wm') wm1 =
    (List.range m₁).foldl (fun wm' j =>
      ((vals j).enumFrom (j * m₂)).foldl (fun acc x => acc.write x.1 x.2) wm') wm2 := by
  apply Memory.eq_of_toList_eq
  obtain ⟨h1, _⟩ := block_scatter_loop_inv m₁ m₂ wm1 vals hlen hwm1 m₁ (le_refl m₁)
  obtain ⟨h2, _⟩ := block_scatter_loop_inv m₁ m₂ wm2 vals hlen hwm2 m₁ (le_refl m₁)
  rw [h1, h2]
  congr 1
  have hlen1 : wm1.toList.length = m₁ * m₂ := by
    simp only [Memory.toList, Memory.size] at hwm1; rw [Array.length_toList]; exact hwm1
  have hlen2 : wm2.toList.length = m₁ * m₂ := by
    simp only [Memory.toList, Memory.size] at hwm2; rw [Array.length_toList]; exact hwm2
  rw [List.drop_of_length_le (by omega), List.drop_of_length_le (by omega)]
