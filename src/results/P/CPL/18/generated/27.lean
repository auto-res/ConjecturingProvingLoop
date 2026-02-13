

theorem P1_subsingleton {X : Type*} [TopologicalSpace X] [Subsingleton X] {A : Set X} : Topology.P1 A := by
  have hP2 : Topology.P2 (A : Set X) := P2_subsingleton (X := X) (A := A)
  exact P2_implies_P1 (A := A) hP2

theorem exists_dense_superset_P3 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : Dense A) : ∃ U : Set X, A ⊆ U ∧ IsOpen U ∧ Topology.P3 U := by
  refine ⟨(Set.univ : Set X), ?_, ?_, ?_⟩
  · intro _ _; trivial
  · exact isOpen_univ
  · simpa using (P3_univ (X := X))

theorem P2_countable_iUnion {X : Type*} [TopologicalSpace X] {A : ℕ → Set X} (hA : ∀ n, Topology.P2 (A n)) : Topology.P2 (⋃ n, A n) := by
  simpa using (P2_iUnion (X := X) (A := A) hA)