

theorem P2_implies_P1 {A : Set X} : P2 A → P1 A := by
  intro h
  exact h.trans interior_subset