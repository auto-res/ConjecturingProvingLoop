

theorem Topology.P1_of_P2_closed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) (hP2 : Topology.P2 A) : Topology.P1 A := by
  have hP3 : Topology.P3 A := Topology.P2_implies_P3 hP2
  exact Topology.P1_of_P3_closed (A := A) hA hP3