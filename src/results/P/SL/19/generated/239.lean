

theorem Topology.frontier_eq_empty_of_closure_eq_interior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : closure A = interior A) :
    frontier A = (∅ : Set X) := by
  simpa [frontier, h, Set.diff_self]