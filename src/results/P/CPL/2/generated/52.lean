

theorem exists_open_P3 {X : Type*} [TopologicalSpace X] [Nonempty X] : ∃ U : Set X, IsOpen U ∧ Topology.P3 (X:=X) U := by
  refine ⟨(Set.univ : Set X), isOpen_univ, ?_⟩
  simpa using (P3_univ (X := X))