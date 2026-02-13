

theorem closure_diff_subset_left {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A \ B) ⊆ closure A := by
  have h : A \ B ⊆ A := Set.diff_subset
  exact closure_mono h