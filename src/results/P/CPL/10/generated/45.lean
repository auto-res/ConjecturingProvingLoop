

theorem exists_nowhere_dense_P1 {X : Type*} [TopologicalSpace X] : ∃ A : Set X, closure A = A ∧ interior A = (∅ : Set X) ∧ Topology.P1 A := by
  refine ⟨(∅ : Set X), ?_, ?_, ?_⟩
  · simp
  · simp
  · intro x hx
    cases hx