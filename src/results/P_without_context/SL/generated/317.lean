

theorem P2_imp_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : P2 (A := A)) : P1 (A := A) := by
  dsimp [P1, P2] at *
  exact Set.Subset.trans hA interior_subset