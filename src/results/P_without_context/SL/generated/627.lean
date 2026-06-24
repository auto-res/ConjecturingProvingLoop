

theorem P2_implies_P1 {A : Set X} : P2 A → P1 A := by
  intro hP2
  dsimp [P2] at hP2
  dsimp [P1]
  intro x hx
  exact interior_subset (hP2 hx)