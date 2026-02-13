

theorem frontier_closure_eq_frontier_of_closed {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : IsClosed A) :
    frontier (closure A) = frontier A := by
  simpa [hA.closure_eq]