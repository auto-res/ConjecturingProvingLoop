

theorem P1_and_P3_equiv_P2 {X : Type*} [TopologicalSpace X] {A : Set X} : (Topology.P1 A ∧ Topology.P3 A) ↔ Topology.P2 A := by
  constructor
  · exact P1_and_P3_implies_P2
  · intro hP2
    exact ⟨P1_of_P2 hP2, P3_of_P2 hP2⟩

theorem exists_open_dense_subset_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P1 A → ∃ U, IsOpen U ∧ U ⊆ A ∧ closure U = closure A := by
  intro hP1
  refine ⟨interior A, isOpen_interior, interior_subset, ?_⟩
  exact (P1_iff_closure_interior_eq_closure).1 hP1