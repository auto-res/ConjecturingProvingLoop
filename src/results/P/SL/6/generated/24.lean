

theorem P2_iff_open_of_closed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed (A : Set X)) : Topology.P2 A ↔ IsOpen A := by
  constructor
  · intro hP2
    have hP3 : Topology.P3 A := Topology.P2_implies_P3 hP2
    exact (Topology.P3_iff_open_of_closed (A := A) hA).1 hP3
  · intro hOpen
    exact Topology.open_satisfies_P2 (A := A) hOpen