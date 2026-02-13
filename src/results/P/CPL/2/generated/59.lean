

theorem exists_disjoint_P3 {X : Type*} [TopologicalSpace X] [Nonempty X] : ∃ A B : Set X, A ∩ B = ∅ ∧ Topology.P3 (X:=X) A ∧ Topology.P3 (X:=X) B := by
  refine ⟨(∅ : Set X), (Set.univ : Set X), ?_, ?_, ?_⟩
  · simp
  · simpa using (Topology.P3_empty (X := X))
  · simpa using (Topology.P3_univ (X := X))