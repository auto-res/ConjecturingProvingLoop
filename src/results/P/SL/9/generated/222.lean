

theorem Topology.closureFrontier_eq_self
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (frontier A) = frontier A := by
  have h_closed : IsClosed (frontier A) := isClosed_frontier
  simpa using h_closed.closure_eq