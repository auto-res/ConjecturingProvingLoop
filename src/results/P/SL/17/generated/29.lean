

theorem Topology.closure_interior_eq_closure_of_P2 {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP2 : Topology.P2 A) :
    closure (interior A) = closure A := by
  have hP1 : Topology.P1 A := Topology.P2_implies_P1 (A := A) hP2
  exact Topology.closure_interior_eq_closure_of_P1 (A := A) hP1