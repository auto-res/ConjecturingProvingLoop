

theorem P2_implies_P1 {A : Set X} (h : P2 A) : P1 A := by
  dsimp [P2, P1] at h ⊢
  exact Set.Subset.trans h (by
    simpa using interior_subset (s := closure (interior A)))