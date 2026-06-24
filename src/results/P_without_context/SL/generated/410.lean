

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    P2 A → P3 A := by
  intro h
  dsimp [P2, P3] at h
  refine Set.Subset.trans h ?_
  have hsub : closure (interior A) ⊆ closure A :=
    closure_mono (interior_subset : interior A ⊆ A)
  exact interior_mono hsub