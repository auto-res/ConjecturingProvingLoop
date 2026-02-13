

theorem Topology.frontier_eq_closure_of_empty_interior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : interior (A : Set X) = (∅ : Set X)) :
    frontier (A : Set X) = closure A := by
  simpa [frontier, h] using
    (by
      simp [frontier, h])