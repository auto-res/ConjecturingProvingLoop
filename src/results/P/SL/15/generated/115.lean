

theorem interior_closure_eq_interior_of_isClosed {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA_closed : IsClosed A) :
    interior (closure A) = interior A := by
  simpa [hA_closed.closure_eq]