

theorem P2_implies_P1 {A : Set X} : P2 A → P1 A := by
  intro hP2
  dsimp [P2, P1] at *
  have hSub : interior (closure (interior A)) ⊆ closure (interior A) := by
    simpa using
      (interior_subset : interior (closure (interior A)) ⊆ closure (interior A))
  exact subset_trans hP2 hSub