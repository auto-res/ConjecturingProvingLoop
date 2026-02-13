

theorem exists_disjoint_P1 {X : Type*} [TopologicalSpace X] [Nonempty X] : ∃ A B : Set X, A ∩ B = ∅ ∧ Topology.P1 (X:=X) A ∧ Topology.P1 (X:=X) B := by
  refine ⟨(∅ : Set X), (Set.univ : Set X), ?_, ?_, ?_⟩
  · simp
  · simpa using (P1_empty (X := X))
  · simpa using (P1_univ (X := X))