

theorem P2_implies_P1 {A : Set X} (hA : P2 A) : P1 A := by
  dsimp [P2, P1] at *
  exact fun x hx => interior_subset (hA hx)