

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    P2 (A : Set X) → P1 A := by
  intro h
  dsimp [P2] at h
  dsimp [P1]
  exact Set.Subset.trans h interior_subset