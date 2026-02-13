

theorem closure_iUnion_interior_subset_closure_interior_iUnion
    {ι : Sort _} {X : Type _} [TopologicalSpace X] (A : ι → Set X) :
    closure (⋃ i, interior (A i : Set X)) ⊆
      closure (interior (⋃ i, A i : Set X)) := by
  -- First, show that the union of the interiors is contained in the
  -- interior of the union.
  have hSub :
      (⋃ i, interior (A i : Set X)) ⊆ interior (⋃ i, A i : Set X) := by
    intro y hy
    rcases Set.mem_iUnion.1 hy with ⟨i, hyInt⟩
    -- `interior (A i)` sits inside the desired interior by monotonicity.
    have hIntSub :
        interior (A i : Set X) ⊆ interior (⋃ j, A j : Set X) := by
      apply interior_mono
      intro z hz
      exact Set.mem_iUnion.2 ⟨i, hz⟩
    exact hIntSub hyInt
  -- Taking closures preserves inclusions.
  exact closure_mono hSub