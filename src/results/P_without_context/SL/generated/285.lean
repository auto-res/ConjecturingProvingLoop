

theorem P2_implies_P3 {A : Set X} : P2 A → P3 A := by
  intro hP2
  dsimp [P2, P3] at hP2
  have hsubset : interior (closure (interior A)) ⊆ interior (closure A) := by
    have hcl : closure (interior A) ⊆ closure A := by
      have : interior A ⊆ A := interior_subset
      exact closure_mono this
    exact interior_mono hcl
  exact hP2.trans hsubset