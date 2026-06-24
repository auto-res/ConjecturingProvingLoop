

theorem P2_implies_P1_and_P3
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : P2 A) : P1 A ∧ P3 A := by
  -- Prove P1
  have hP1 : P1 A := by
    dsimp [P1] at *
    intro x hx
    have hx' : x ∈ interior (closure (interior A)) := h hx
    exact interior_subset hx'
  -- Prove P3
  have hP3 : P3 A := by
    dsimp [P3] at *
    intro x hx
    have hx' : x ∈ interior (closure (interior A)) := h hx
    have hsubset : interior (closure (interior A)) ⊆ interior (closure A) := by
      have hcl : closure (interior A) ⊆ closure A := by
        have : interior A ⊆ A := interior_subset
        exact closure_mono this
      exact interior_mono hcl
    exact hsubset hx'
  exact And.intro hP1 hP3