

theorem P2_implies_P1 {A : Set X} : P2 A → P1 A := by
  intro h
  unfold P2 at h
  unfold P1
  exact Set.Subset.trans h interior_subset