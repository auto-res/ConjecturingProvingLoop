

theorem Topology.isOpen_P3_iff_P1_and_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen A) :
    Topology.P3 (X := X) A ↔
      (Topology.P1 (X := X) A ∧ Topology.P2 (X := X) A) := by
  -- Existing equivalences for open sets.
  have hP1P3 : Topology.P1 (X := X) A ↔ Topology.P3 (X := X) A :=
    Topology.isOpen_P1_iff_P3 (X := X) (A := A) hOpen
  have hP1P2 : Topology.P1 (X := X) A ↔ Topology.P2 (X := X) A :=
    Topology.isOpen_P1_iff_P2 (X := X) (A := A) hOpen
  -- Build the desired equivalence.
  constructor
  · intro hP3
    -- Obtain `P1` from `P3`, and then `P2` from `P1`.
    have hP1 : Topology.P1 (X := X) A := (hP1P3).mpr hP3
    have hP2 : Topology.P2 (X := X) A := (hP1P2).1 hP1
    exact And.intro hP1 hP2
  · rintro ⟨hP1, _⟩
    -- From `P1`, deduce `P3`.
    exact (hP1P3).1 hP1