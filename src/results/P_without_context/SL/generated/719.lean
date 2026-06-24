

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : P2 (A := A)) : P1 (A := A) := by
  dsimp [P1, P2] at *
  intro x hx
  have hx' : x ∈ interior (closure (interior A)) := h hx
  exact interior_subset hx'