

theorem Topology.frontier_eq_closure_diff_interior
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    frontier (A : Set X) = closure A \ interior A := by
  rfl