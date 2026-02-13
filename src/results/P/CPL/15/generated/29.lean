

theorem closure_eq_interior_closure_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P2 A) : closure (interior (closure A)) = closure A := by
  simpa using (P3_dense (A := A) (P2_subset_P3 (A := A) hA)).symm

theorem exists_open_dense_subset_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P1 A) : ∃ U, IsOpen U ∧ closure U = closure A := by
  refine ⟨interior A, isOpen_interior, ?_⟩
  simpa using (closure_eq_of_P1 (A := A) hA).symm

theorem P2_closed_iff_interior_eq {X : Type*} [TopologicalSpace X] {A : Set X} (hcl : IsClosed A) : P2 A ↔ interior A = A := by
  constructor
  · intro hP2
    apply Set.Subset.antisymm
    · exact interior_subset
    · intro x hxA
      have hx_int_cl : x ∈ interior (closure (interior A)) := hP2 hxA
      rcases mem_interior.1 hx_int_cl with ⟨U, hU_sub, hU_open, hxU⟩
      have h_closure_subset : (closure (interior A) : Set X) ⊆ A := by
        have : (closure (interior A) : Set X) ⊆ closure A :=
          closure_mono (interior_subset : (interior A : Set X) ⊆ A)
        simpa [hcl.closure_eq] using this
      have hU_subA : (U : Set X) ⊆ A := hU_sub.trans h_closure_subset
      exact mem_interior.2 ⟨U, hU_subA, hU_open, hxU⟩
  · intro h_int_eq
    intro x hxA
    have hx_int : x ∈ interior A := by
      simpa [h_int_eq] using hxA
    have h_subset :
        (interior A : Set X) ⊆ interior (closure (interior A)) :=
      interior_maximal
        (subset_closure : (interior A : Set X) ⊆ closure (interior A))
        isOpen_interior
    exact h_subset hx_int