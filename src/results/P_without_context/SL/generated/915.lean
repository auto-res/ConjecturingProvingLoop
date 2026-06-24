

theorem P2_to_P3 {A : Set X} (h : P2 A) : P3 A := by
  dsimp [P2, P3] at *
  have hle1 : closure (interior A) ⊆ closure A :=
    closure_mono interior_subset
  have hle2 : interior (closure (interior A)) ⊆ interior (closure A) :=
    interior_mono hle1
  exact h.trans hle2