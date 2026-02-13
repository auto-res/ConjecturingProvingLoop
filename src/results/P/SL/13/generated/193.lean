

theorem Topology.P2_iff_closure_eq_closureInterior_and_P3 {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    Topology.P2 (X := X) A ↔
      (closure (A : Set X) = closure (interior A) ∧ Topology.P3 (X := X) A) := by
  -- Step 1: use the existing equivalence between `P2` and `P1 ∧ P3`.
  have h₁ :=
    Topology.P2_iff_P1_and_P3 (X := X) (A := A)
  -- Step 2: rewrite the `P1` component via the closure‐equality characterization.
  have h₂ :
      (Topology.P1 (X := X) A ∧ Topology.P3 (X := X) A) ↔
        (closure (A : Set X) = closure (interior A) ∧ Topology.P3 (X := X) A) := by
    constructor
    · rintro ⟨hP1, hP3⟩
      have h_eq :=
        (Topology.P1_iff_closure_eq_closureInterior (X := X) (A := A)).1 hP1
      exact ⟨h_eq, hP3⟩
    · rintro ⟨h_eq, hP3⟩
      have hP1 :
          Topology.P1 (X := X) A :=
        (Topology.P1_iff_closure_eq_closureInterior (X := X) (A := A)).2 h_eq
      exact ⟨hP1, hP3⟩
  exact h₁.trans h₂