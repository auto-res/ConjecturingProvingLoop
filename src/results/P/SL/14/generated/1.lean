

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    P2 A → P3 A := by
  intro h
  dsimp [P2, P3] at h ⊢
  have h1 : interior (closure (interior A)) ⊆ interior (closure A) := by
    have hsubset : closure (interior A) ⊆ closure A :=
      closure_mono (interior_subset : interior A ⊆ A)
    exact interior_mono hsubset
  exact Set.Subset.trans h h1