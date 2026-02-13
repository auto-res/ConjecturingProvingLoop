

theorem Topology.frontier_eq_frontier_interior_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A := A) → frontier A = frontier (interior A) := by
  intro hP2
  have hClos : closure A = closure (interior A) :=
    Topology.closure_eq_closure_interior_of_P2 (A := A) hP2
  simp [frontier, hClos, interior_interior]