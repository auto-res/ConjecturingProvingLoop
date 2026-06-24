

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} (h : P2 (A : Set X)) : P1 A := by
  unfold P1 P2 at *
  intro x hxA
  exact interior_subset (h hxA)