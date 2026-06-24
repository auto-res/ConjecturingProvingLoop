

theorem P2_imp_P1 {A : Set X} (hA : P2 A) : P1 A := by
  intro x hxA
  exact interior_subset (hA hxA)