

theorem P2_implies_P1 {A : Set X} : P2 A → P1 A := by
  intro hP2 x hxA
  exact interior_subset (hP2 hxA)