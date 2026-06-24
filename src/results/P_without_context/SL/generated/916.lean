

theorem P2_implies_P1 {A : Set X} (h : P2 A) : P1 A := by
  dsimp [P2, P1] at *
  intro x hx
  have hx' : x ∈ interior (closure (interior A)) := h hx
  exact interior_subset hx'