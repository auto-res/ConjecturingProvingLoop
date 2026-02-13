

theorem exists_compact_subset_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P2 A → ∃ K, IsCompact K ∧ K ⊆ A := by
  intro _
  refine ⟨(∅ : Set X), ?_⟩
  refine ⟨isCompact_empty, ?_⟩
  intro x hx
  cases hx