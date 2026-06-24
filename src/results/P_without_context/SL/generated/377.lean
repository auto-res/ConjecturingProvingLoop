

theorem P2_implies_P3 {A : Set X} : P2 A → P3 A := by
  intro hP2
  dsimp [P2] at hP2
  dsimp [P3]
  intro x hxA
  have hclosure : closure (interior A) ⊆ closure A := by
    apply closure_mono
    exact interior_subset
  have hinterior : interior (closure (interior A)) ⊆ interior (closure A) := by
    apply interior_mono
    exact hclosure
  exact hinterior (hP2 hxA)