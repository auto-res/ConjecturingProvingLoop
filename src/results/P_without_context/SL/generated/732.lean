

theorem P2_implies_P1 {A : Set X} (h : P2 A) : P1 A := by
  dsimp [P2] at h
  dsimp [P1]
  exact subset_trans h interior_subset