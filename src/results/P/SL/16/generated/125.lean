

theorem Topology.isOpen_P1_iff_P2_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen A) :
    Topology.P1 (X := X) A ↔
      (Topology.P2 (X := X) A ∧ Topology.P3 (X := X) A) := by
  -- We already know `P1 ↔ P2` and `P1 ↔ P3` for open sets.
  have hP1P2 : Topology.P1 (X := X) A ↔ Topology.P2 (X := X) A :=
    Topology.isOpen_P1_iff_P2 (X := X) (A := A) hOpen
  have hP1P3 : Topology.P1 (X := X) A ↔ Topology.P3 (X := X) A :=
    Topology.isOpen_P1_iff_P3 (X := X) (A := A) hOpen
  constructor
  · intro hP1
    have hP2 : Topology.P2 (X := X) A := (hP1P2).1 hP1
    have hP3 : Topology.P3 (X := X) A := (hP1P3).1 hP1
    exact And.intro hP2 hP3
  · rintro ⟨hP2, _⟩
    exact (hP1P2).2 hP2