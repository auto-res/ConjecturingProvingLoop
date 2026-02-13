

theorem P1_univ {X : Type*} [TopologicalSpace X] : P1 (Set.univ : Set X) := by
  intro x hx
  simpa [interior_univ, closure_univ] using hx

theorem P2_univ {X : Type*} [TopologicalSpace X] : P2 (Set.univ : Set X) := by
  intro x hx
  simpa [interior_univ, closure_univ] using hx

theorem P3_empty {X : Type*} [TopologicalSpace X] : P3 (∅ : Set X) := by
  intro x hx
  cases hx