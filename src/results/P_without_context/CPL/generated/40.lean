

theorem P3_of_P2 {A : Set X} : P2 A → P3 A := by
  intro hP2
  have h_step : interior (closure (interior (A : Set X))) ⊆ interior (closure A) :=
    interior_mono (closure_mono interior_subset)
  exact Set.Subset.trans hP2 h_step