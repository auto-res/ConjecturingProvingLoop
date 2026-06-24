

theorem P2_implies_P1 {A : Set X} (h : P2 A) : P1 A := by
  unfold P1 P2 at *
  intro x hx
  exact interior_subset (h hx)