

theorem closure_interior_eq_of_closed_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) (hP2 : Topology.P2 A) :
    closure (interior A) = A := by
  have hP1 : Topology.P1 A := Topology.P2_implies_P1 hP2
  exact Topology.closure_interior_eq_of_closed_P1 hA hP1