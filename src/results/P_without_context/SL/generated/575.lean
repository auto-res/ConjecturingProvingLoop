

theorem P2_imp_P1 {A : Set X} : P2 A → P1 A := by
  intro h
  dsimp [P2, P1] at h ⊢
  intro x hx
  exact interior_subset (h hx)