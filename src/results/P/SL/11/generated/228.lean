

theorem interior_subset_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior A ⊆ closure (interior A) := by
  exact subset_closure