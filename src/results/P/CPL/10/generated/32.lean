

theorem exists_nontrivial_P2 {X : Type*} [TopologicalSpace X] [Nonempty X] : ∃ A : Set X, A.Nonempty ∧ Topology.P2 A := by
  classical
  obtain ⟨x⟩ := ‹Nonempty X›
  refine ⟨(Set.univ : Set X), ?_, ?_⟩
  · exact ⟨x, by simp⟩
  · simpa using (P2_univ (X := X))

theorem exists_dense_P1_closed {X : Type*} [TopologicalSpace X] : ∃ A : Set X, IsClosed A ∧ Dense A ∧ Topology.P1 A := by
  refine ⟨(Set.univ : Set X), isClosed_univ, dense_univ, ?_⟩
  simpa using Topology.P1_univ (X := X)