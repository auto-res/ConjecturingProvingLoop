

theorem P2_imp_P1 {A : Set X} (h : P2 A) : P1 A := by
  dsimp [P1, P2] at *
  intro x hx
  have hx' : x ∈ interior (closure (interior A)) := h hx
  have : x ∈ closure (interior A) :=
    (interior_subset : interior (closure (interior A)) ⊆ closure (interior A)) hx'
  exact this