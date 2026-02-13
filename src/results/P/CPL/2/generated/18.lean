

theorem P2_mk_mem {X : Type*} [TopologicalSpace X] (x : X) : ∃ A : Set X, x ∈ A ∧ Topology.P2 (X:=X) A := by
  refine ⟨(Set.univ : Set X), ?_, ?_⟩
  · simp
  · simpa using P2_univ (X := X)

theorem exists_compact_P1 {X : Type*} [TopologicalSpace X] [CompactSpace X] : ∃ A : Set X, IsCompact A ∧ Topology.P1 (X:=X) A := by
  refine ⟨(Set.univ : Set X), ?_, ?_⟩
  · simpa using isCompact_univ
  · simpa using (Topology.P1_univ (X := X))