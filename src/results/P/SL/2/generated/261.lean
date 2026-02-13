

theorem Topology.frontier_eq_self_diff_interior_of_isClosed {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    IsClosed A → frontier (A : Set X) = A \ interior A := by
  intro hClosed
  simpa [frontier, hClosed.closure_eq]