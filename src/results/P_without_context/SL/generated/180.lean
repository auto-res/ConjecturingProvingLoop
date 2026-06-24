

theorem P2_implies_P1 {A : Set X} : P2 A → P1 A := by
  intro hA
  dsimp [P2] at hA
  dsimp [P1]
  intro x hx
  have : x ∈ interior (closure (interior A)) := hA hx
  exact interior_subset this