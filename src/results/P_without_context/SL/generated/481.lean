

theorem P2_implies_P1 {A : Set X} (hA : P2 A) : P1 A := by
  unfold P2 at hA
  unfold P1
  intro x hx
  exact (interior_subset (s := closure (interior A))) (hA hx)