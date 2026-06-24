

theorem P2_implies_P1 {A : Set X} : P2 (A := A) → P1 (A := A) := by
  intro hA
  unfold P1 P2 at *
  exact Set.Subset.trans hA interior_subset