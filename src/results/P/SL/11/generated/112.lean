

theorem interior_subset_closure_of_set {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior A ⊆ closure A := by
  exact interior_subset.trans subset_closure