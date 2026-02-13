

theorem exists_countable_P1 {X : Type*} [TopologicalSpace X] : ∃ A : Set X, Set.Countable A ∧ Topology.P1 A := by
  refine ⟨(∅ : Set X), Set.countable_empty, ?_⟩
  intro x hx
  cases hx