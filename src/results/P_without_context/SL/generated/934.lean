

theorem P2_implies_P1 {A : Set X} : P2 A → P1 A := by
  intro h
  unfold P1 P2 at *
  exact h.trans interior_subset