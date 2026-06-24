

theorem P2_imp_P1 {A : Set X} : P2 A → P1 A := by
  intro h
  exact Set.Subset.trans h interior_subset