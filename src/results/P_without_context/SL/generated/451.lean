

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    P2 A → P1 A := by
  intro hP2
  dsimp [P2] at hP2
  dsimp [P1]
  exact hP2.trans (interior_subset (s := closure (interior A)))