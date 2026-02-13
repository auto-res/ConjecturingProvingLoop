

theorem exists_dense_open_P3_superset {X : Type*} [TopologicalSpace X] {A : Set X} : ∃ U, IsOpen U ∧ Dense U ∧ A ⊆ U ∧ Topology.P3 U := by
  refine ⟨(Set.univ : Set X), isOpen_univ, dense_univ, Set.subset_univ _, ?_⟩
  exact P3_univ (X := X)

theorem P3_iinter {X : Type*} [TopologicalSpace X] {A B : Set X} : Topology.P3 (interior A ∩ interior B) := by
  have h_open : IsOpen (interior A ∩ interior B) :=
    (isOpen_interior : IsOpen (interior A)).inter isOpen_interior
  exact P3_of_open (A := interior A ∩ interior B) h_open