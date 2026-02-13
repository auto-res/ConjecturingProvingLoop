

theorem closure_eq_closure_interior_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 A) :
    closure A = closure (interior A) := by
  have hP1 : Topology.P1 A := Topology.P2_implies_P1 hP2
  exact Topology.closure_eq_closure_interior_of_P1 hP1