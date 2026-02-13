

theorem P1_iff_P2_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P1 A ↔ Topology.P2 A := by
  constructor
  · intro _h
    exact Topology.isOpen_implies_P2 (X := X) (A := A) hA
  · intro hP2
    exact Topology.P2_implies_P1 (X := X) (A := A) hP2