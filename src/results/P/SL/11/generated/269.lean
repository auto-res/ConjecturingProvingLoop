

theorem exists_open_subset_same_closure_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 A) :
    ∃ U : Set X, IsOpen U ∧ U ⊆ A ∧ closure U = closure A := by
  refine ⟨interior A, isOpen_interior, interior_subset, ?_⟩
  have hEq :
      closure (interior A) = closure A :=
    (Topology.closure_eq_closure_interior_of_P1 (A := A) hP1).symm
  simpa [hEq]