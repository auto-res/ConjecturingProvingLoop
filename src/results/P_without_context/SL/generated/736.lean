

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    P2 A → P1 A := by
  intro hP2
  dsimp [P2, P1] at *
  intro x hxA
  exact interior_subset (hP2 hxA)