

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    P2 (A := A) → P1 (A := A) := by
  intro h
  dsimp [P2, P1] at *
  intro x hx
  exact
    (interior_subset : interior (closure (interior A)) ⊆ closure (interior A)) (h hx)