

theorem P2_implies_P3 {A : Set X} : P2 A → P3 A := by
  intro hP2
  unfold P2 at hP2
  unfold P3
  exact
    Set.Subset.trans hP2
      (interior_mono
        (closure_mono
          (interior_subset : interior A ⊆ A)))