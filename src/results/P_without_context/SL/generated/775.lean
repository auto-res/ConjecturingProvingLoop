

theorem P2_implies_P1 {A : Set X} (h : P2 A) : P1 A :=
by
  dsimp [P1, P2] at *
  exact Set.Subset.trans h (interior_subset (s := closure (interior A)))