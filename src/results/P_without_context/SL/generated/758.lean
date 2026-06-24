

theorem P2_implies_P3 {A : Set X} (h : P2 A) : P3 A := by
  intro x hx
  exact (interior_mono (closure_mono interior_subset)) (h hx)