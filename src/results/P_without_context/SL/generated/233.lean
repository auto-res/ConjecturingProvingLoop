

theorem P2_implies_P3 {A : Set X} (hA : P2 A) : P3 A := by
  dsimp [P2] at hA
  dsimp [P3]
  intro x hx
  have hx₁ : x ∈ interior (closure (interior A)) := hA hx
  have hmono : interior (closure (interior A)) ⊆ interior (closure A) :=
    interior_mono (closure_mono interior_subset)
  exact hmono hx₁