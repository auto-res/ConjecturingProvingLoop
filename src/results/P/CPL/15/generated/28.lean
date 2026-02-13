

theorem P2_of_P3_and_closed {X : Type*} [TopologicalSpace X] {A : Set X} (h3 : P3 A) (h_closed : IsClosed A) : P2 A := by
  intro x hx
  -- First, use `h3` to place `x` in `interior (closure A)`.
  have hx_int_closure : x ∈ interior (closure A) := h3 hx
  -- Since `A` is closed, `closure A = A`.
  have h_closure_eq : closure A = A := h_closed.closure_eq
  -- Hence `x ∈ interior A`.
  have hx_int : x ∈ interior A := by
    simpa [h_closure_eq] using hx_int_closure
  -- `interior A` is contained in `interior (closure (interior A))`.
  have h_subset : (interior A : Set X) ⊆ interior (closure (interior A)) :=
    interior_maximal (subset_closure : (interior A : Set X) ⊆ closure (interior A))
      isOpen_interior
  -- Conclude the desired membership.
  exact h_subset hx_int