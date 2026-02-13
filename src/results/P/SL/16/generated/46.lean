

theorem Topology.isOpen_P2_iff_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen A) :
    Topology.P2 (X := X) A ↔ Topology.P3 (X := X) A := by
  -- Since `A` is open, it satisfies both `P2` and `P3`.
  have hP2 : Topology.P2 (X := X) A :=
    Topology.isOpen_implies_P2 (X := X) (A := A) hOpen
  have hP3 : Topology.P3 (X := X) A :=
    Topology.isOpen_implies_P3 (X := X) (A := A) hOpen
  constructor
  · intro _; exact hP3
  · intro _; exact hP2