

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    P2 A → P1 A := by
  intro hA
  dsimp [P2] at hA
  dsimp [P1]
  exact Set.Subset.trans hA interior_subset