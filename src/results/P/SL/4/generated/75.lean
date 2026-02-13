

theorem interior_subset_closure_set {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior A ⊆ closure A := by
  intro x hx
  exact subset_closure (interior_subset hx)