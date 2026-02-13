

theorem closed_of_eq_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (A : Set X)) = A → IsClosed (A : Set X) := by
  intro hEq
  simpa [hEq] using
    (isClosed_closure :
      IsClosed (closure (interior (A : Set X))))