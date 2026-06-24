

theorem P2_implies_P1 {A : Set X} : P2 A → P1 A := by
  dsimp [P2, P1]
  intro hA
  exact subset_trans hA interior_subset