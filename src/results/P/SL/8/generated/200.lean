

theorem interior_diff_subset_left {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (A \ B) ⊆ interior A := by
  have h : A \ B ⊆ A := Set.diff_subset
  exact interior_mono h