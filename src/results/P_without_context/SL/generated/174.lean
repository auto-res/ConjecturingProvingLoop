

theorem P2_imp_P1 {A : Set X} : P2 A → P1 A := by
  intro h
  unfold P1 P2 at *
  exact subset_trans h interior_subset