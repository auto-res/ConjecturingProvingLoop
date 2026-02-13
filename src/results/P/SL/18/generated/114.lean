

theorem interior_closure_eq_interior_of_closed
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed (A : Set X)) :
    interior (closure (A : Set X)) = interior (A : Set X) := by
  simpa [hA_closed.closure_eq]