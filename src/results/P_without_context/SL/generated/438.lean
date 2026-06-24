

theorem P2_implies_P1 {A : Set X} : P2 A → P1 A := by
  intro hA
  unfold P2 P1 at *
  exact hA.trans interior_subset