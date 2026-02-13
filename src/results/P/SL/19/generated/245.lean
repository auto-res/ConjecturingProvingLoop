

theorem Topology.frontier_interior_eq_frontier_of_isOpen
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) :
    frontier (interior A) = frontier A := by
  have hInt : interior A = A := hA.interior_eq
  simpa [frontier, hInt, interior_interior]