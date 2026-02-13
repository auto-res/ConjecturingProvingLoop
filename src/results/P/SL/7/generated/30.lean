

theorem Topology.P1_iff_exists_open_dense_subset {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A ↔ ∃ U : Set X, IsOpen U ∧ U ⊆ A ∧ closure U = closure A := by
  classical
  have hEq := Topology.P1_iff_closure_eq_closureInterior (A := A)
  constructor
  · intro hP1
    refine ⟨interior A, isOpen_interior, interior_subset, ?_⟩
    have h : closure A = closure (interior A) := (hEq).1 hP1
    exact h.symm
  · rintro ⟨U, hU_open, hU_subset, hClosureEq⟩
    dsimp [Topology.P1]
    intro x hxA
    have hx_closureU : x ∈ closure U := by
      have hx_closureA : x ∈ closure A := subset_closure hxA
      simpa [hClosureEq.symm] using hx_closureA
    have hU_subset_int : U ⊆ interior A := by
      intro y hyU
      have hy_intU : y ∈ interior U := by
        simpa [hU_open.interior_eq] using hyU
      exact (interior_mono hU_subset) hy_intU
    have hClosure_subset : closure U ⊆ closure (interior A) := closure_mono hU_subset_int
    exact hClosure_subset hx_closureU