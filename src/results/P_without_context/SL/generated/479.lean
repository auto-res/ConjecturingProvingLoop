

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : P2 (A := A)) : P1 (A := A) := by
  dsimp [P2, P1] at *
  exact h.trans interior_subset