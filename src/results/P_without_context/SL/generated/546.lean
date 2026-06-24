

theorem P2_implies_P3 {A : Set X} :
    P2 (A := A) → P3 (A := A) :=
by
  intro h
  dsimp [P2, P3] at *
  intro x hx
  have hx' : x ∈ interior (closure (interior A)) := h hx
  have hsubset : interior (closure (interior A)) ⊆ interior (closure A) :=
    interior_mono (closure_mono interior_subset)
  exact hsubset hx'