

theorem P2_implies_P3 {A : Set X} :
    P2 (A := A) → P3 (A := A) := by
  intro hP2
  dsimp [P2] at hP2
  dsimp [P3]
  intro x hx
  have hx' : x ∈ interior (closure (interior A)) := hP2 hx
  have h_subset : interior (closure (interior A)) ⊆ interior (closure A) :=
    interior_mono (closure_mono interior_subset)
  exact h_subset hx'