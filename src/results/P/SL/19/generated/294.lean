

theorem Topology.frontier_eq_closure_of_empty_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} (hInt : interior A = (∅ : Set X)) :
    frontier A = closure A := by
  simpa [frontier, hInt]