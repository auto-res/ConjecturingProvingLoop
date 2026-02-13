

theorem frontier_interior_closure_subset_frontier
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    frontier (interior (closure A)) ⊆ frontier A := by
  intro x hx
  -- Unpack `hx` into the two conditions defining the frontier.
  have hx_cl  : x ∈ closure (interior (closure A)) := hx.1
  have hx_nint : x ∉ interior (interior (closure A)) := hx.2
  -- `closure (interior (closure A))` is contained in `closure A`.
  have h_sub_cl : closure (interior (closure A)) ⊆ closure A :=
    closure_interior_closure_subset_closure (X := X) (A := A)
  have hx_clA : x ∈ closure A := h_sub_cl hx_cl
  -- Show that `x` is not in `interior A`.
  have hx_nintA : x ∉ interior A := by
    intro hx_intA
    -- `interior A ⊆ interior (closure A)`.
    have h_sub_int : (interior A : Set X) ⊆ interior (closure A) :=
      interior_subset_interior_closure (A := A)
    have hx_int_clA : x ∈ interior (closure A) := h_sub_int hx_intA
    -- Rewrite `interior (closure A)` as `interior (interior (closure A))`.
    have : x ∈ interior (interior (closure A)) := by
      simpa [interior_interior] using hx_int_clA
    exact hx_nint this
  -- Conclude that `x` lies in the frontier of `A`.
  exact And.intro hx_clA hx_nintA