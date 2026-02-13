

theorem Topology.closure_frontier_eq_frontier {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (frontier A) = frontier A := by
  have hClosed : IsClosed (frontier A) := by
    simpa using (Topology.isClosed_boundary (X := X) (A := A))
  simpa using hClosed.closure_eq