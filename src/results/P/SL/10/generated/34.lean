

theorem Topology.P1_iff_P2_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P1 A ↔ Topology.P2 A := by
  have hP1 : Topology.P1 A :=
    Topology.isOpen_implies_P1 (X := X) (A := A) hA
  have hP2 : Topology.P2 A :=
    Topology.isOpen_implies_P2 (X := X) (A := A) hA
  constructor
  · intro _; exact hP2
  · intro _; exact hP1