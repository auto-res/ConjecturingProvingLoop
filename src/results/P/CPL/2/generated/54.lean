

theorem exists_compact_P3 {X : Type*} [TopologicalSpace X] [CompactSpace X] : ∃ K : Set X, IsCompact K ∧ Topology.P3 (X:=X) K := by
  refine ⟨(Set.univ : Set X), ?_, ?_⟩
  · simpa using isCompact_univ
  · simpa using (P3_univ (X := X))