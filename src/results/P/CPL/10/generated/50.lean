

theorem exists_nonempty_closed_P2 {X : Type*} [TopologicalSpace X] [Nonempty X] : ∃ A : Set X, IsClosed A ∧ A.Nonempty ∧ Topology.P2 A := by
  refine ⟨(Set.univ : Set X), isClosed_univ, ?_, ?_⟩
  ·
    obtain ⟨x⟩ := (‹Nonempty X›)
    exact ⟨x, by simp⟩
  ·
    simpa using Topology.P2_univ (X := X)