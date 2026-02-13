

theorem exists_open_dense_P2 {X : Type*} [TopologicalSpace X] : ∃ U : Set X, IsOpen U ∧ Dense U ∧ Topology.P2 U := by
  exact ⟨(Set.univ : Set X), isOpen_univ, dense_univ, Topology.P2_univ (X := X)⟩