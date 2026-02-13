

theorem exists_open_P2_superset {X} [TopologicalSpace X] {A : Set X} (h : P2 A) : ∃ U, IsOpen U ∧ A ⊆ U ∧ P2 U := by
  refine ⟨(Set.univ : Set X), isOpen_univ, Set.subset_univ _, ?_⟩
  simpa using P2_univ (X := X)