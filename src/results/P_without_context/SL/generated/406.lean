

theorem P2_implies_P3 :
    ∀ (X : Type*) [TopologicalSpace X] (A : Set X), P2 (A : Set X) → P3 A := by
  intro X _ A hP2
  dsimp [P2] at hP2
  dsimp [P3]
  have hsubset : interior (closure (interior A)) ⊆ interior (closure A) := by
    apply interior_mono
    apply closure_mono
    exact interior_subset
  exact subset_trans hP2 hsubset