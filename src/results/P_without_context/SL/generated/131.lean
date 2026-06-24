

theorem P2_imp_P1_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : P2 (A := A)) : P1 A ∧ P3 A := by
  dsimp [P2] at h
  dsimp [P1, P3]
  refine And.intro ?_ ?_
  · exact Set.Subset.trans h interior_subset
  ·
    have h_sub : interior (closure (interior A)) ⊆ interior (closure A) := by
      have : closure (interior A) ⊆ closure A := by
        exact closure_mono interior_subset
      exact interior_mono this
    exact Set.Subset.trans h h_sub