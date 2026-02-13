

theorem closure_interior_closure_interior_closure_idempotent
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure (interior (closure (A : Set X))))) =
      closure (interior (closure (A : Set X))) := by
  simpa using
    (closure_interior_closure_interior_idempotent
      (X := X) (A := closure (A : Set X)))