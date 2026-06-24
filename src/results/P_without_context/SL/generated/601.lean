

theorem P2_implies_P1 {A : Set X} : P2 A → P1 A := by
  intro h
  dsimp [P2, P1] at *
  refine subset_trans h ?_
  simpa using interior_subset (s := closure (interior A))