

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} (h : P2 A) : P1 A := by
  dsimp [P1, P2] at *
  intro x hx
  exact interior_subset (h hx)