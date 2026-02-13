

theorem P2_subset_P1 (A : Set X) : P2 A → P1 A := by
  intro h
  exact h.trans interior_subset

theorem P2_imp_P3 (A : Set X) : P2 A → P3 A := by
  intro h
  exact h.trans (interior_mono (closure_mono interior_subset))