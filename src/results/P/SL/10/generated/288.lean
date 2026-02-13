

theorem Topology.boundary_eq_empty_iff_open_and_closed {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    closure A \ interior A = (∅ : Set X) ↔ (IsOpen A ∧ IsClosed A) := by
  classical
  constructor
  · intro h
    -- First show `closure A ⊆ interior A`.
    have h_subset : closure A ⊆ interior A := by
      intro x hx_cl
      by_cases hx_int : x ∈ interior A
      · exact hx_int
      ·
        -- Otherwise `x` would lie in the (empty) boundary.
        have h_mem : x ∈ closure A \ interior A := ⟨hx_cl, hx_int⟩
        have h_false : False := by
          have : x ∈ (∅ : Set X) := by
            simpa [h] using h_mem
          simpa using this
        exact (h_false.elim)
    -- Hence `interior A = A`.
    have h_int_eq : interior A = A := by
      apply Set.Subset.antisymm
      · exact interior_subset
      · intro x hxA
        exact h_subset (subset_closure hxA)
    -- And `closure A = A`.
    have h_cl_eq : closure A = A := by
      apply Set.Subset.antisymm
      · intro x hx_cl
        have : x ∈ interior A := h_subset hx_cl
        exact interior_subset this
      · exact subset_closure
    -- Conclude that `A` is both open and closed.
    have hOpen : IsOpen A := by
      have : IsOpen (interior A) := isOpen_interior
      simpa [h_int_eq] using this
    have hClosed : IsClosed A := by
      have : IsClosed (closure A) := isClosed_closure
      simpa [h_cl_eq] using this
    exact And.intro hOpen hClosed
  · rintro ⟨hOpen, hClosed⟩
    -- For an open and closed set the boundary is empty.
    have h_int_eq : interior A = A := hOpen.interior_eq
    have h_cl_eq  : closure A = A  := hClosed.closure_eq
    simpa [h_int_eq, h_cl_eq, Set.diff_self]