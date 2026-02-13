

theorem exists_measurable_P2 {X : Type*} [TopologicalSpace X] [MeasurableSpace X] : ∃ A : Set X, MeasurableSet A ∧ Topology.P2 A := by
  refine ⟨(Set.univ : Set X), ?_, ?_⟩
  · simpa using MeasurableSet.univ
  · simpa using Topology.P2_univ (X := X)

theorem exists_measurable_P1 {X : Type*} [TopologicalSpace X] [MeasurableSpace X] : ∃ A : Set X, MeasurableSet A ∧ Topology.P1 A := by
  refine ⟨(Set.univ : Set X), ?_, ?_⟩
  · simpa using MeasurableSet.univ
  · simpa using Topology.P1_univ (X := X)

theorem exists_measurable_P3 {X : Type*} [TopologicalSpace X] [MeasurableSpace X] : ∃ A : Set X, MeasurableSet A ∧ Topology.P3 A := by
  refine ⟨(Set.univ : Set X), ?_, ?_⟩
  · simpa using MeasurableSet.univ
  · simpa using Topology.P3_univ (X := X)