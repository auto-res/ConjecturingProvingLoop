

theorem P2_implies_P1 {A : Set X} (hA : P2 A) : P1 A := by
  dsimp [P1, P2] at *
  intro x hx
  exact
    (interior_subset : interior (closure (interior A)) ⊆ closure (interior A)) (hA hx)