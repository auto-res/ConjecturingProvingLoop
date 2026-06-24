

theorem P2_implies_P1 {A : Set X} (h : P2 A) : P1 A := by
  dsimp [P2, P1] at *
  exact subset_trans h interior_subset