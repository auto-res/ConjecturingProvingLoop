

theorem P2_iff_P3_of_closed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) :
    Topology.P2 A ↔ Topology.P3 A := by
  have hP2_open : Topology.P2 A ↔ IsOpen A :=
    Topology.P2_closed_iff_open hA_closed
  have hOpen_P3 : IsOpen A ↔ Topology.P3 A :=
    (Topology.P3_closed_iff_open hA_closed).symm
  exact hP2_open.trans hOpen_P3