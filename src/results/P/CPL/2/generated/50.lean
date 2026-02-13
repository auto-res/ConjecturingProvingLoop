

theorem exists_minimal_P1 {X : Type*} [TopologicalSpace X] [Nonempty X] : ∃ A : Set X, Topology.P1 (X:=X) A ∧ ∀ B : Set X, B ⊆ A → Topology.P1 (X:=X) B → B = A := by
  refine ⟨(∅ : Set X), ?_, ?_⟩
  · simpa using (Topology.P1_empty (X := X))
  · intro B hB_subset _hB_P1
    have h_eq : (B : Set X) = ∅ := by
      apply Set.Subset.antisymm hB_subset
      exact Set.empty_subset _
    simpa using h_eq