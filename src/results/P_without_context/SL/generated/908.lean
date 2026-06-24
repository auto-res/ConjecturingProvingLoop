

theorem P2_implies_P3 {A : Set X} (h : P2 A) : P3 A := by
  dsimp [P2] at h
  dsimp [P3]
  intro x hx
  have hx' : x ∈ interior (closure (interior A)) := h hx
  have hsubset : interior (closure (interior A)) ⊆ interior (closure A) :=
    interior_mono (closure_mono interior_subset)
  exact hsubset hx'