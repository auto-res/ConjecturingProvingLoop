

theorem P2_implies_P1 {A : Set X} (hA : P2 A) : P1 A := by
  dsimp [P2, P1] at *
  intro x hx
  have hx_int : x ∈ interior (closure (interior A)) := hA hx
  have hx_cl : x ∈ closure (interior A) :=
    (interior_subset : interior (closure (interior A)) ⊆ closure (interior A)) hx_int
  exact hx_cl