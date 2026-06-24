

theorem P2_imp_P3 {A : Set X} (hA : P2 A) : P3 A :=
by
  dsimp [P2, P3] at *
  intro x hx
  have hx' : x ∈ interior (closure (interior A)) := hA hx
  have h_subset : interior (closure (interior A)) ⊆ interior (closure A) :=
    interior_mono (closure_mono interior_subset)
  exact h_subset hx'