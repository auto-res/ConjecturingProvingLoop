

theorem Topology.isClopen_of_boundary_eq_empty {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : closure (A : Set X) \ interior A = (∅ : Set X)) :
    IsClosed A ∧ IsOpen A := by
  classical
  -- Step 1: `closure A ⊆ interior A`.
  have h_subset : (closure (A : Set X)) ⊆ interior A := by
    intro x hx_cl
    by_contra hx_int
    have : x ∈ closure (A : Set X) \ interior A := ⟨hx_cl, hx_int⟩
    have : x ∈ (∅ : Set X) := by
      simpa [h] using this
    exact this.elim
  -- Step 2: `closure A = interior A`.
  have h_eq_cl_int :
      (closure (A : Set X)) = interior A :=
    Set.Subset.antisymm h_subset
      (Topology.interior_subset_closure (A := A))
  -- Step 3: `closure A = A`.
  have h_cl_eq : (closure (A : Set X)) = A := by
    apply Set.Subset.antisymm
    · intro x hx_cl
      -- `x ∈ closure A = interior A ⊆ A`.
      have : x ∈ interior A := by
        simpa [h_eq_cl_int] using hx_cl
      exact interior_subset this
    · exact subset_closure
  -- Step 4: `interior A = A`.
  have h_int_eq : interior A = A := by
    apply Set.Subset.antisymm
    · exact interior_subset
    · intro x hxA
      have hx_cl : x ∈ closure (A : Set X) := subset_closure hxA
      have : x ∈ interior A := h_subset hx_cl
      exact this
  -- Step 5: conclude `A` is clopen.
  have h_closed : IsClosed A := by
    have : IsClosed (closure (A : Set X)) := isClosed_closure
    simpa [h_cl_eq] using this
  have h_open : IsOpen A := by
    have : IsOpen (interior A) := isOpen_interior
    simpa [h_int_eq] using this
  exact ⟨h_closed, h_open⟩