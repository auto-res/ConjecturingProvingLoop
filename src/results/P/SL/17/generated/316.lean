

theorem Topology.frontier_eq_closure_of_interior_empty
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hInt : interior A = (∅ : Set X)) :
    frontier A = closure A := by
  simpa [frontier, hInt, Set.diff_empty]