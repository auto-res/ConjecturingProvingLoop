

theorem exists_open_dense_superset_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P1 A) : ∃ U, IsOpen U ∧ A ⊆ U ∧ closure U = Set.univ := by
  refine ⟨(Set.univ : Set X), isOpen_univ, ?_, ?_⟩
  · intro x hx; trivial
  · simpa using closure_univ