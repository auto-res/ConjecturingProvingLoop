

theorem P2_iff_P3_of_open {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) :
    Topology.P2 A ↔ Topology.P3 A := by
  have hP1P2 : Topology.P1 A ↔ Topology.P2 A :=
    Topology.P1_iff_P2_of_open hA
  have hP1P3 : Topology.P1 A ↔ Topology.P3 A :=
    Topology.P1_iff_P3_of_open hA
  exact hP1P2.symm.trans hP1P3