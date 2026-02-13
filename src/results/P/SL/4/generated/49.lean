

theorem P1_iff_P2_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) :
    Topology.P1 A ↔ Topology.P2 A := by
  constructor
  · intro _hP1
    exact Topology.isOpen_P2 (A := A) hA
  · intro _hP2
    exact Topology.isOpen_P1 (A := A) hA