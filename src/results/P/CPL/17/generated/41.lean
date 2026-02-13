

theorem exists_open_dense_P2_superset {X : Type*} [TopologicalSpace X] {A : Set X} : ∃ U, IsOpen U ∧ Dense U ∧ A ⊆ U ∧ Topology.P2 U := by
  refine ⟨(Set.univ : Set X), isOpen_univ, dense_univ, Set.subset_univ _, ?_⟩
  exact P2_univ (X := X)

theorem P2_Union_closed {X : Type*} [TopologicalSpace X] {ι : Sort*} {f : ι → Set X} (h_closed : ∀ i, IsClosed (f i)) : (∀ i, Topology.P2 (f i)) → Topology.P2 (⋃ i, f i) := by
  intro hP2
  exact P2_iUnion (X := X) (f := f) hP2