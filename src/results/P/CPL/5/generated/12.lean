

theorem P2_union_three {X : Type*} [TopologicalSpace X] {A B C : Set X} (hA : P2 A) (hB : P2 B) (hC : P2 C) : P2 (A ∪ B ∪ C) := by
  -- First, merge `A` and `B`.
  have hAB : P2 (A ∪ B) := P2_union hA hB
  -- Then, merge the result with `C`.
  have hABC : P2 ((A ∪ B) ∪ C) := P2_union hAB hC
  -- Rewrite with associativity of union.
  simpa [Set.union_assoc] using hABC

theorem P3_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} (hA : P3 A) (hB : P3 B) : P3 (Set.image (fun x : X × Y => (x.1, x.2)) (A ×ˢ B)) := by
  intro x hx
  rcases hx with ⟨⟨a, b⟩, hmem, rfl⟩
  have ha : a ∈ interior (closure A) := hA hmem.1
  have hb : b ∈ interior (closure B) := hB hmem.2
  have hprod : (a, b) ∈ interior (closure A) ×ˢ interior (closure B) := by
    exact ⟨ha, hb⟩
  simpa [closure_prod_eq, interior_prod_eq] using hprod

theorem P1_bUnion {X : Type*} [TopologicalSpace X] {ι : Sort _} {s : Set ι} (f : ι → Set X) (h : ∀ i ∈ s, P1 (f i)) : P1 (⋃ i ∈ s, f i) := by
  intro x hx
  rcases Set.mem_iUnion.mp hx with ⟨i, hx_i⟩
  rcases Set.mem_iUnion.mp hx_i with ⟨hi_mem_s, hx_fi⟩
  have hP1 : P1 (f i) := h i hi_mem_s
  have hx_cl : x ∈ closure (interior (f i)) := hP1 hx_fi
  have hsubset :
      closure (interior (f i)) ⊆ closure (interior (⋃ i ∈ s, f i)) := by
    have hsub : (f i : Set X) ⊆ ⋃ i ∈ s, f i := by
      intro y hy
      -- membership in the inner union over proofs `i ∈ s`
      have hinner : y ∈ ⋃ (hi : i ∈ s), f i := by
        refine Set.mem_iUnion.mpr ?_
        exact ⟨hi_mem_s, hy⟩
      -- membership in the outer union over indices `i`
      refine Set.mem_iUnion.mpr ?_
      exact ⟨i, hinner⟩
    exact closure_mono (interior_mono hsub)
  exact hsubset hx_cl