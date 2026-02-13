

theorem exists_compact_P3 {X : Type*} [TopologicalSpace X] : ∃ K : Set X, IsCompact K ∧ Topology.P3 K := by
  exact ⟨(∅ : Set X), isCompact_empty, (P3_empty (X := X))⟩