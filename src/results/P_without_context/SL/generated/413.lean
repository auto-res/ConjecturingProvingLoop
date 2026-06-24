

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    P2 (A := A) → P1 (A := A) := by
  intro hP2
  dsimp [P2] at hP2
  dsimp [P1]
  exact Set.Subset.trans hP2 interior_subset