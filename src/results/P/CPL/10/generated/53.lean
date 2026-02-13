

theorem exists_dense_P1_measurable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] : ∃ A : Set X, MeasurableSet A ∧ Dense A ∧ Topology.P1 A := by
  refine ⟨(Set.univ : Set X), ?_, ?_, ?_⟩
  · simpa using MeasurableSet.univ
  · simpa using dense_univ
  · simpa using Topology.P1_univ (X := X)