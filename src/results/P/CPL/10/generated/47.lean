

theorem exists_dense_closed_nonempty_P3 {X : Type*} [TopologicalSpace X] [Nonempty X] : ∃ A : Set X, A.Nonempty ∧ Dense A ∧ IsClosed A ∧ Topology.P3 A := by
  classical
  obtain ⟨x⟩ := ‹Nonempty X›
  refine ⟨(Set.univ : Set X), ?_, dense_univ, isClosed_univ, ?_⟩
  · exact ⟨x, by simp⟩
  · simpa using Topology.P3_univ (X := X)