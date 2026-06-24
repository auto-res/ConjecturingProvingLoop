

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    P2 (A := A) → P1 (A := A) := by
  intro h
  unfold P2 at h
  unfold P1
  exact subset_trans h interior_subset