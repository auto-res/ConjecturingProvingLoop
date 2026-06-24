

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    P2 (X := X) A → P1 (X := X) A := by
  intro hA
  unfold P2 P1 at *
  exact subset_trans hA interior_subset