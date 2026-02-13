

theorem interior_eq_closure_iff_clopen
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior A = closure A ↔ (IsOpen A ∧ IsClosed A) := by
  constructor
  · intro h_eq
    -- First, show `interior A = A`.
    have hA_int : A ⊆ interior A := by
      intro x hx
      have hx_cl : x ∈ closure A := subset_closure hx
      simpa [h_eq] using hx_cl
    have h_int_eq : interior A = A :=
      subset_antisymm interior_subset hA_int
    -- Next, deduce `closure A = A`.
    have h_cl_eq : closure A = A := by
      calc
        closure A = interior A := by
          simpa [h_eq]
        _ = A := h_int_eq
    -- Conclude that `A` is both open and closed.
    have h_open : IsOpen A := by
      have : IsOpen (interior A) := isOpen_interior
      simpa [h_int_eq] using this
    have h_closed : IsClosed A := by
      have : IsClosed (closure A) := isClosed_closure
      simpa [h_cl_eq] using this
    exact And.intro h_open h_closed
  · rintro ⟨h_open, h_closed⟩
    simpa [h_open.interior_eq, h_closed.closure_eq]