

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P2 (X := X) A) :
    P1 A := by
  dsimp [P2, P1] at hA
  exact subset_trans hA interior_subset