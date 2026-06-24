

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    P2 (A := A) → P1 (A := A) := by
  intro hP2
  unfold P2 at hP2
  unfold P1
  intro x hxA
  exact interior_subset (hP2 hxA)