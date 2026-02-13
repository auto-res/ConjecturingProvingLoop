

theorem Topology.P1_iff_P2_of_P3
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP3 : Topology.P3 A) :
    Topology.P1 A ↔ Topology.P2 A := by
  constructor
  · intro hP1
    exact Topology.P2_of_P1_and_P3 (A := A) hP1 hP3
  · intro hP2
    exact P2_implies_P1 (A := A) hP2