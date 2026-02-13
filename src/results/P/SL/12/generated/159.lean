

theorem Topology.P2_iff_P1_and_P3_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen (A : Set X)) :
    Topology.P2 (X := X) A ↔
      (Topology.P1 (X := X) A ∧ Topology.P3 (X := X) A) := by
  -- Existing equivalences for open sets.
  have h₁ : Topology.P1 (X := X) A ↔ Topology.P2 (X := X) A :=
    Topology.P1_iff_P2_of_isOpen (X := X) (A := A) hA
  have h₂ : Topology.P1 (X := X) A ↔ Topology.P3 (X := X) A :=
    Topology.P1_iff_P3_of_isOpen (X := X) (A := A) hA
  constructor
  · intro hP2
    -- Obtain `P1` from `P2`, then `P3` from `P1`.
    have hP1 : Topology.P1 (X := X) A := h₁.mpr hP2
    have hP3 : Topology.P3 (X := X) A := h₂.mp hP1
    exact And.intro hP1 hP3
  · rintro ⟨hP1, _⟩
    -- Convert `P1` back to `P2`.
    exact h₁.mp hP1