

theorem P3_of_P2 {A : Set X} (h : P2 A) : P3 A := by
  dsimp [P2, P3] at *
  intro x hx
  have hx₁ : x ∈ interior (closure (interior A)) := h hx
  have hsubset : closure (interior A) ⊆ closure A :=
    closure_mono interior_subset
  exact (interior_mono hsubset) hx₁