

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    P2 (A : Set X) → P3 A := by
  intro h
  dsimp [P2] at h
  dsimp [P3]
  apply subset_trans h
  apply interior_mono
  apply closure_mono
  exact interior_subset