

theorem P2_implies_P3 {A : Set X} : P2 A → P3 A := by
  intro hP2
  dsimp [P2] at hP2
  dsimp [P3]
  have h_subset : interior (closure (interior A)) ⊆ interior (closure A) := by
    have h_closure : closure (interior A) ⊆ closure A := by
      simpa using closure_mono interior_subset
    exact interior_mono h_closure
  exact Set.Subset.trans hP2 h_subset