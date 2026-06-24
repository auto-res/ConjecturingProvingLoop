

theorem P2_implies_P1 {A : Set X} : P2 A → P1 A := by
  intro hP2
  dsimp [P1, P2] at hP2 ⊢
  exact Set.Subset.trans hP2 interior_subset