

theorem Topology.frontier_closure_eq_frontier_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) :
    frontier (closure A) = frontier A := by
  simpa [frontier, hA.closure_eq, closure_closure]