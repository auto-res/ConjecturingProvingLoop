

theorem Topology.frontier_eq_self_diff_interior_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) :
    frontier A = A \ interior A := by
  simpa [frontier, hA.closure_eq]