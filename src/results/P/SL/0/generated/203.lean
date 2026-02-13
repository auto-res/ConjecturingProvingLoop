

theorem P1_iff_P2_and_P3_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen (A : Set X)) :
    Topology.P1 A ↔ (Topology.P2 A ∧ Topology.P3 A) := by
  -- Equivalences already established for open sets.
  have h₁ : Topology.P1 A ↔ Topology.P2 A :=
    Topology.P1_iff_P2_of_isOpen (X := X) (A := A) hA
  have h₂ : Topology.P2 A ↔ Topology.P3 A :=
    Topology.P2_iff_P3_of_isOpen (X := X) (A := A) hA
  -- Assemble the desired equivalence.
  constructor
  · intro hP1
    have hP2 : Topology.P2 A := h₁.mp hP1
    have hP3 : Topology.P3 A := h₂.mp hP2
    exact And.intro hP2 hP3
  · rintro ⟨hP2, _⟩
    exact h₁.mpr hP2