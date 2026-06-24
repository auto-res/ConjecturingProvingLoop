

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    P2 A → P1 A := by
  intro hP2
  dsimp [P2] at hP2
  dsimp [P1]
  have h_int : interior (closure (interior A)) ⊆ closure (interior A) :=
    interior_subset
  exact subset_trans hP2 h_int