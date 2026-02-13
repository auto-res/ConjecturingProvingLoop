

theorem P1_unionᵢ {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} : (∀ i, P1 (A i)) → P1 (⋃ i, A i) := by
  intro hP1
  intro x hxUnion
  rcases Set.mem_iUnion.1 hxUnion with ⟨i, hxAi⟩
  -- Use the hypothesis for the chosen index.
  have hP1i : P1 (A i) := hP1 i
  have hx_cl : x ∈ closure (interior (A i)) := hP1i hxAi
  -- Relate the closures/interiors of the individual set and the big union.
  have h_subset : closure (interior (A i)) ⊆ closure (interior (⋃ j, A j)) := by
    -- First, relate the interiors.
    have h_int : interior (A i) ⊆ interior (⋃ j, A j) := by
      have hAi_sub : (A i : Set X) ⊆ ⋃ j, A j := by
        intro y hy
        exact Set.mem_iUnion.2 ⟨i, hy⟩
      exact interior_mono hAi_sub
    -- Then take closures.
    exact closure_mono h_int
  exact h_subset hx_cl

theorem P3_of_dense_subset {X : Type*} [TopologicalSpace X] {A B : Set X} : A ⊆ B → closure A = Set.univ → P3 B := by
  intro hAB hDense
  -- First, show that `closure B = univ`.
  have hDenseB : closure (B : Set X) = Set.univ := by
    apply Set.Subset.antisymm
    · exact Set.subset_univ _
    · intro x _
      -- Since `closure A = univ`, every point is in `closure A`,
      -- and hence (by monotonicity) in `closure B`.
      have hxA : x ∈ closure (A : Set X) := by
        simpa [hDense] using (Set.mem_univ x)
      exact (closure_mono hAB) hxA
  -- Now apply the previously proved lemma.
  exact P3_of_dense (A := B) hDenseB