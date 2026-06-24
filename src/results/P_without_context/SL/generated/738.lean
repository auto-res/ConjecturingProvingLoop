

theorem P2_implies_P1 {A : Set X} (hA : P2 A) : P1 A := by
  intro x hx
  exact interior_subset (hA hx)