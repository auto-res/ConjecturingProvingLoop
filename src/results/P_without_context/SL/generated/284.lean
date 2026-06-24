

theorem P2_implies_P3 {A : Set X} : P2 A → P3 A := by
  intro hP2
  dsimp [P2] at hP2
  dsimp [P3]
  intro x hxA
  have hx : x ∈ interior (closure (interior A)) := hP2 hxA
  have hsubset : interior (closure (interior A)) ⊆ interior (closure A) := by
    have hcl : closure (interior A) ⊆ closure A := by
      exact closure_mono interior_subset
    exact interior_mono hcl
  exact hsubset hx