

theorem Topology.P3_iff_P1_and_P2_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen (A : Set X)) :
    Topology.P3 (X := X) A ↔
      (Topology.P1 (X := X) A ∧ Topology.P2 (X := X) A) := by
  -- Established equivalences for open sets.
  have h₁ : Topology.P1 (X := X) A ↔ Topology.P3 (X := X) A :=
    Topology.P1_iff_P3_of_isOpen (X := X) (A := A) hA
  have h₂ : Topology.P2 (X := X) A ↔ Topology.P3 (X := X) A :=
    Topology.P2_iff_P3_of_isOpen (X := X) (A := A) hA
  constructor
  · intro hP3
    -- Derive `P1` and `P2` from `P3`.
    have hP1 : Topology.P1 (X := X) A := h₁.mpr hP3
    have hP2 : Topology.P2 (X := X) A := h₂.mpr hP3
    exact And.intro hP1 hP2
  · rintro ⟨hP1, _⟩
    -- Recover `P3` from `P1`.
    exact h₁.mp hP1