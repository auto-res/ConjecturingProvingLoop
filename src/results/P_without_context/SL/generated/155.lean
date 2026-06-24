

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    P2 (A := A) → P1 (A := A) := by
  intro h
  dsimp [P1, P2] at *
  exact Set.Subset.trans h interior_subset