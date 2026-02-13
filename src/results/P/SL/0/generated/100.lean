

theorem closure_interior_closure_subset_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure (A : Set X))) ⊆ closure (A : Set X) := by
  simpa [closure_closure] using
    (closure_interior_subset_closure_self
      (X := X) (A := closure (A : Set X)))