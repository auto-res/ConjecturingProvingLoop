

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    P2 (X := X) A → P1 (X := X) A := by
  intro h
  dsimp [P1, P2] at *
  exact subset_trans h (interior_subset : interior (closure (interior A)) ⊆ closure (interior A))