

theorem Topology.isOpen_P2_iff_P1_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen A) :
    Topology.P2 (X := X) A ↔
      (Topology.P1 (X := X) A ∧ Topology.P3 (X := X) A) := by
  -- Equivalences between `P1`, `P2`, and `P3` for open sets.
  have hP1P2 : Topology.P1 (X := X) A ↔ Topology.P2 (X := X) A :=
    Topology.isOpen_P1_iff_P2 (X := X) (A := A) hOpen
  have hP1P3 : Topology.P1 (X := X) A ↔ Topology.P3 (X := X) A :=
    Topology.isOpen_P1_iff_P3 (X := X) (A := A) hOpen
  constructor
  · intro hP2
    -- Obtain `P1` from `P2`.
    have hP1 : Topology.P1 (X := X) A := (hP1P2).2 hP2
    -- Obtain `P3` from `P1`.
    have hP3 : Topology.P3 (X := X) A := (hP1P3).1 hP1
    exact And.intro hP1 hP3
  · rintro ⟨hP1, _⟩
    -- Obtain `P2` from `P1`.
    exact (hP1P2).1 hP1