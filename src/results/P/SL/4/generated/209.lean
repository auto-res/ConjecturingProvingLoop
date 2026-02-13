

theorem interior_inter_interior_closure_eq
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior A ∩ interior (closure A) = interior A := by
  ext x
  constructor
  · intro hx
    exact hx.1
  · intro hx
    -- `interior A` is contained in `interior (closure A)` by monotonicity.
    have h_subset : interior A ⊆ interior (closure A) :=
      interior_mono (subset_closure : (A : Set X) ⊆ closure A)
    have hx_int_cl : x ∈ interior (closure A) := h_subset hx
    exact And.intro hx hx_int_cl