

theorem Topology.isOpen_P1_iff_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen A) :
    Topology.P1 (X := X) A ↔ Topology.P3 (X := X) A := by
  have hP1_of_open : Topology.P1 (X := X) A :=
    Topology.isOpen_implies_P1 (X := X) (A := A) hOpen
  have hP3_of_open : Topology.P3 (X := X) A :=
    Topology.isOpen_implies_P3 (X := X) (A := A) hOpen
  constructor
  · intro _; exact hP3_of_open
  · intro _; exact hP1_of_open