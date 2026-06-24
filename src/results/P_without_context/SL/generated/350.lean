

theorem P2_implies_P1 {A : Set X} (h : P2 (A := A)) : P1 (A := A) := by
  dsimp [P1, P2] at h ⊢
  exact h.trans interior_subset