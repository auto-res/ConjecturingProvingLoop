

theorem Topology.frontier_interior_eq_closureInterior_diff_interior
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    frontier (interior A) = closure (interior A) \ interior A := by
  simp [frontier, interior_interior]