

theorem P2_implies_P1 {A : Set X} : P2 A → P1 A := by
  intro hP2
  dsimp [P2] at hP2
  dsimp [P1]
  intro x hx
  have : x ∈ interior (closure (interior A)) := hP2 hx
  exact (interior_subset (s := closure (interior A))) this