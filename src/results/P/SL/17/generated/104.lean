

theorem Topology.P1_iff_P2_and_P3_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P1 A ↔ (Topology.P2 A ∧ Topology.P3 A) := by
  -- Pairwise equivalences already established for open sets
  have h₁ : Topology.P1 A ↔ Topology.P2 A :=
    Topology.P1_iff_P2_of_isOpen (A := A) hA
  have h₂ : Topology.P1 A ↔ Topology.P3 A :=
    Topology.P1_iff_P3_of_isOpen (A := A) hA
  -- Combine them to obtain the desired equivalence
  constructor
  · intro hP1
    exact ⟨(h₁.mp hP1), (h₂.mp hP1)⟩
  · rintro ⟨hP2, _hP3⟩
    exact h₁.mpr hP2