

theorem exists_open_superset_same_closure_of_P3
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 A →
      ∃ U : Set X, IsOpen U ∧ A ⊆ U ∧ closure U = closure A := by
  intro hP3
  refine ⟨interior (closure A), isOpen_interior, ?_, ?_⟩
  ·
    exact hP3
  ·
    simpa using
      (Topology.closure_eq_closure_interior_closure_of_P3 (A := A) hP3).symm