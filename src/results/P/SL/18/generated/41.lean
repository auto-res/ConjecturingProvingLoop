

theorem P1_iff_P2_of_open {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) :
    Topology.P1 A ↔ Topology.P2 A := by
  constructor
  · intro _hP1
    exact Topology.P2_of_open hA
  · intro hP2
    exact Topology.P2_implies_P1 hP2