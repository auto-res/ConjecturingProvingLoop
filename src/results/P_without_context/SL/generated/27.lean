

theorem P2_implies_P1 {A : Set X} : P2 A → P1 A := by
  dsimp [P2, P1]
  intro h x hx
  exact interior_subset (h hx)