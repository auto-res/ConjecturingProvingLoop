

theorem P2_implies_P3 {A : Set X} (h : P2 A) : P3 A := by
  dsimp [P2, P3] at *
  intro x hxA
  have hxInt : x ∈ interior (closure (interior A)) := h hxA
  have h_closure_subset : closure (interior A) ⊆ closure A :=
    closure_mono interior_subset
  have h_int_subset : interior (closure (interior A)) ⊆ interior (closure A) :=
    interior_mono h_closure_subset
  exact h_int_subset hxInt