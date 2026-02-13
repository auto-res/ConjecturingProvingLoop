

theorem interior_diff_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (A \ B : Set X) ⊆ interior A := by
  exact interior_mono (Set.diff_subset)