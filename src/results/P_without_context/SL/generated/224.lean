

theorem P2_implies_P1 {A : Set X} : P2 A → P1 A := by
  intro h
  exact fun x hx => interior_subset (h hx)