

theorem exists_nonempty_P2 {X : Type*} [TopologicalSpace X] [Nonempty X] : ∃ A : Set X, A.Nonempty ∧ Topology.P2 (X:=X) A := by
  obtain ⟨x₀⟩ := (inferInstance : Nonempty X)
  refine ⟨(Set.univ : Set X), ?_, ?_⟩
  · exact ⟨x₀, by simp⟩
  · simpa using (P2_univ (X := X))