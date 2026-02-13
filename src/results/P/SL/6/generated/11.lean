

theorem closure_interior_subset_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior A) ⊆ closure A := by
  exact closure_mono interior_subset