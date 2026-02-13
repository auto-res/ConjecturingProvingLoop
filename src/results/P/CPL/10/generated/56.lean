

theorem exists_dense_P3_measurable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] : ∃ A : Set X, MeasurableSet A ∧ Topology.P3 A ∧ Dense A := by
  refine ⟨(Set.univ : Set X), ?_, ?_, ?_⟩
  · simpa using MeasurableSet.univ
  · simpa using Topology.P3_univ (X := X)
  · simpa using dense_univ