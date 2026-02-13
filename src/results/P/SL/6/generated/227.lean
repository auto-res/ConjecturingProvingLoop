

theorem interior_subset_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (A : Set X) ⊆ closure A := by
  exact interior_subset.trans subset_closure