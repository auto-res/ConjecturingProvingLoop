

theorem closure_interior_closure_eq_closure_interior_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed (A : Set X)) :
    closure (interior (closure (A : Set X))) =
      closure (interior (A : Set X)) := by
  simpa [hA_closed.closure_eq]