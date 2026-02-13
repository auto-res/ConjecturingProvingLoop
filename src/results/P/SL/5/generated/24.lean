

theorem closure_interior_closure_subset_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure A)) ⊆ closure A := by
  have h : (interior (closure A) : Set X) ⊆ closure A := interior_subset
  simpa using closure_mono h