

theorem P2_implies_P1 {A : Set X} : P2 A → P1 A := by
  intro h x hx
  exact interior_subset (h hx)