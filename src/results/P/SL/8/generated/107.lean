

theorem closure_interior_subset_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior A) ⊆ closure A := by
  have h : interior A ⊆ A := interior_subset
  exact closure_mono h