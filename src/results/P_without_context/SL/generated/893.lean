

theorem P2_implies_P1 {A : Set X} : P2 A → P1 A := by
  intro hA
  unfold P2 at hA
  unfold P1
  exact Set.Subset.trans hA (interior_subset)