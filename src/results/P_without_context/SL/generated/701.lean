

theorem P2_imp_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    P2 (A := A) → P1 (A := A) := by
  intro hP2
  intro x hxA
  exact interior_subset (hP2 hxA)