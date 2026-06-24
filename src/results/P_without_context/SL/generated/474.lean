

theorem P2_implies_P1 {A : Set X} (h : P2 A) : P1 A := by
  dsimp [P2, P1] at *
  have h₂ : interior (closure (interior A)) ⊆ closure (interior A) :=
    interior_subset
  exact subset_trans h h₂