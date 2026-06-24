

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    P2 (X := X) A → P1 (X := X) A := by
  intro h
  exact subset_trans h interior_subset