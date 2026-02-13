

theorem Topology.P1_iff_P2_and_P3_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen (A : Set X)) :
    Topology.P1 A ↔ (Topology.P2 A ∧ Topology.P3 A) := by
  -- Existing equivalences under the openness assumption.
  have h₁ : Topology.P1 A ↔ Topology.P2 A :=
    Topology.P1_iff_P2_of_isOpen (A := A) hA
  have h₂ : Topology.P1 A ↔ Topology.P3 A :=
    Topology.P1_iff_P3_of_isOpen (A := A) hA
  -- Prove the desired equivalence.
  constructor
  · intro hP1
    exact ⟨h₁.mp hP1, h₂.mp hP1⟩
  · rintro ⟨hP2, _⟩
    exact h₁.mpr hP2