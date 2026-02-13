

theorem P2_exists_compact_subset {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P2 A → ∃ K, IsCompact K ∧ K ⊆ A := by
  intro _hP2
  exact ⟨(∅ : Set X), isCompact_empty, Set.empty_subset _⟩