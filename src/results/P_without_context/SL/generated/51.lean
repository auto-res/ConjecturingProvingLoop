

theorem P2_implies_P1 (A : Set X) (hA : P2 A) : P1 A := by
  dsimp [P2] at hA
  dsimp [P1]
  intro x hx
  have hx' : x ∈ interior (closure (interior A)) := hA hx
  exact interior_subset hx'