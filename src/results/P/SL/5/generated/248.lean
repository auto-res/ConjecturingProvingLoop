

theorem P2_iff_P1_of_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP3 : Topology.P3 (X := X) A) :
    Topology.P2 (X := X) A ↔ Topology.P1 (X := X) A := by
  -- Start with the established equivalence `P2 ↔ P1 ∧ P3`.
  have h₁ := Topology.P2_iff_P1_and_P3 (X := X) (A := A)
  -- Given the assumption `P3 A`, simplify the right side of the equivalence.
  have h₂ :
      (Topology.P1 (X := X) A ∧ Topology.P3 (X := X) A) ↔
        Topology.P1 (X := X) A := by
    constructor
    · intro h
      exact h.1
    · intro hP1
      exact ⟨hP1, hP3⟩
  -- Combine the two equivalences.
  exact h₁.trans h₂