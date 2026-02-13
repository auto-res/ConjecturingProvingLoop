

theorem Topology.frontier_eq_closure_diff_self_of_isOpen
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen (A : Set X)) :
    frontier (A : Set X) = closure A \ A := by
  simpa [frontier, hA.interior_eq]