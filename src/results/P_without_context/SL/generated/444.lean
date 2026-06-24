

theorem P2_implies_P1 {A : Set X} : P2 A → P1 A := by
  intro h
  dsimp [P2, P1] at *
  intro x hx
  have : x ∈ interior (closure (interior A)) := h hx
  exact interior_subset this