

theorem Topology.closure_diff_interior_eq_frontier {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    closure A \ interior A = frontier A := by
  rfl