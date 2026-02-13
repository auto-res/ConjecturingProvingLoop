

theorem Topology.frontier_interior_eq_closure_interior_diff_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    frontier (interior A) = closure (interior A) \ interior A := by
  simpa [frontier, interior_interior]