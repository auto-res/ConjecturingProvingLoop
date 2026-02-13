

theorem interior_closure_subset_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    (interior (closure (A : Set X)) : Set X) ⊆
      closure (interior (closure (A : Set X))) := by
  simpa using
    (subset_closure :
      (interior (closure (A : Set X)) : Set X) ⊆
        closure (interior (closure (A : Set X))))