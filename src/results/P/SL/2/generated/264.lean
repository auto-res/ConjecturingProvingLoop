

theorem Topology.closure_frontier_eq_frontier {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (frontier (A : Set X)) = frontier (A : Set X) := by
  have hClosed : IsClosed (frontier (A : Set X)) := isClosed_frontier
  simpa using hClosed.closure_eq