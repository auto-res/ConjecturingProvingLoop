

theorem closure_diff_subset_left {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A \ B) ⊆ closure A := by
  simpa using
    (closure_mono (Set.diff_subset : (A \ B : Set X) ⊆ A))