

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P2 A) : P1 A := by
  dsimp [P2, P1] at *
  intro x hx
  have hx_int : x ∈ interior (closure (interior A)) := hA hx
  exact interior_subset hx_int