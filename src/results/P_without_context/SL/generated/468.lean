

theorem P2_implies_P1 {A : Set X} : P2 A → P1 A := by
  intro hA
  dsimp [P2, P1] at hA ⊢
  exact hA.trans interior_subset