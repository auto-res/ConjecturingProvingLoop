

theorem P1_empty {X} [TopologicalSpace X] : P1 (∅ : Set X) := by
  intro x hx
  cases hx

theorem P2_empty {X} [TopologicalSpace X] : P2 (∅ : Set X) := by
  intro x hx
  cases hx

theorem P1_univ {X} [TopologicalSpace X] : P1 (Set.univ : Set X) := by
  intro x hx
  simp [interior_univ, closure_univ] at hx
  simpa using hx