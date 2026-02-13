

theorem Topology.boundary_empty_iff_isClopen {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (A : Set X) \ interior A = (∅ : Set X) ↔
      (IsOpen (A : Set X) ∧ IsClosed (A : Set X)) := by
  classical
  constructor
  · intro hEmpty
    -- First, show `closure A ⊆ interior A`.
    have h_subset : closure (A : Set X) ⊆ interior A := by
      intro x hx_cl
      by_contra h_int
      have hx_diff : x ∈ closure (A : Set X) \ interior A := ⟨hx_cl, h_int⟩
      have : x ∈ (∅ : Set X) := by
        simpa [hEmpty] using hx_diff
      exact (Set.not_mem_empty _ this)
    -- Deduce `interior A = A`.
    have h_int_eq : interior (A : Set X) = A := by
      apply Set.Subset.antisymm
      · exact interior_subset
      · intro x hxA
        exact h_subset (subset_closure hxA)
    -- Deduce `closure A = A`.
    have h_cl_eq : closure (A : Set X) = A := by
      apply Set.Subset.antisymm
      · have : closure (A : Set X) ⊆ interior A := h_subset
        simpa [h_int_eq] using this
      · exact subset_closure
    -- Conclude that `A` is both open and closed.
    have h_open : IsOpen (A : Set X) := by
      simpa [h_int_eq] using (isOpen_interior : IsOpen (interior (A : Set X)))
    have h_closed : IsClosed (A : Set X) := by
      simpa [h_cl_eq] using (isClosed_closure : IsClosed (closure (A : Set X)))
    exact And.intro h_open h_closed
  · rintro ⟨h_open, h_closed⟩
    have h_int_eq : interior (A : Set X) = A := h_open.interior_eq
    have h_cl_eq  : closure (A : Set X) = A := h_closed.closure_eq
    simpa [h_int_eq, h_cl_eq, Set.diff_self]