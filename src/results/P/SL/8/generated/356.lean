

theorem interior_inter_subset_left {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (A ∩ B) ⊆ interior A := by
  -- `A ∩ B` is contained in `A`, hence their interiors satisfy the same relation.
  exact interior_mono (Set.inter_subset_left : A ∩ B ⊆ A)