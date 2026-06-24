

theorem P2_implies_P1 {A : Set X} : P2 A → P1 A := by
  intro hP2
  exact Set.Subset.trans hP2 interior_subset