

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    P2 A → P1 A := by
  intro hP2
  dsimp [P2, P1] at *
  intro x hx
  have hx' := hP2 hx
  exact interior_subset hx'