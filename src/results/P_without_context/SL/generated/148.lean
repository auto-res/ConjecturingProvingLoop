

theorem P2_implies_P3 {A : Set X} : P2 A → P3 A := by
  intro hP2
  have hmono : interior (closure (interior A)) ⊆ interior (closure A) := by
    exact interior_mono (closure_mono (interior_subset : interior A ⊆ A))
  exact hP2.trans hmono