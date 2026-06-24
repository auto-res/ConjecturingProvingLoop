

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    P2 (A := A) → P1 (A := A) := by
  intro h
  dsimp [P2] at h
  dsimp [P1]
  exact
    subset_trans h
      (interior_subset :
        interior (closure (interior A)) ⊆ closure (interior A))