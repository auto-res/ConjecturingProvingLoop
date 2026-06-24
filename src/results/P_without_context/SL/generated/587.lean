

theorem P2_imp_P3 (A : Set X) : P2 A → P3 A := by
  intro hA
  dsimp [P2, P3] at *
  have h1 : interior (closure (interior A)) ⊆ interior (closure A) :=
    interior_mono (closure_mono interior_subset)
  exact Set.Subset.trans hA h1