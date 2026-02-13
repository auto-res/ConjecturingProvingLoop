

theorem Dense.closure_eq {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : Dense (A : Set X)) : closure (A : Set X) = (Set.univ : Set X) := by
  ext x
  constructor
  · intro _; simp
  · intro _; exact h x