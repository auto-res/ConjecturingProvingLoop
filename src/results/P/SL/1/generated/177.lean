

theorem Topology.P2_iff_P3_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 A) :
    Topology.P2 A ↔ Topology.P3 A := by
  constructor
  · intro hP2
    exact P2_implies_P3 (A := A) hP2
  · intro hP3
    exact Topology.P2_of_P1_and_P3 (A := A) hP1 hP3