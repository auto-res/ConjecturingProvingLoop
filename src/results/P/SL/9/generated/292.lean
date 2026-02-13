

theorem Topology.frontier_interior_eq_frontier_of_isOpen
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen (A : Set X)) :
    frontier (interior (A : Set X)) = frontier A := by
  simpa [hA.interior_eq]