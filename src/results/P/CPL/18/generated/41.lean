

theorem exists_closed_subset_P1 {X : Type*} [TopologicalSpace X] {A : Set X} : ∃ F : Set X, IsClosed F ∧ F ⊆ A ∧ Topology.P1 F := by
  refine ⟨(∅ : Set X), isClosed_empty, ?_, ?_⟩
  · exact Set.empty_subset _
  · simpa using (P1_empty (X := X))