

theorem frontier_closure_subset_frontier {X : Type*} [TopologicalSpace X] (A : Set X) :
    frontier (closure A) ⊆ frontier A := by
  intro x hx
  -- `hx` gives `x ∈ closure (closure A)` and `x ∉ interior (closure A)`.
  have hx_closureA : x ∈ closure A := by
    simpa [closure_closure] using hx.1
  -- Show that `x` is not in `interior A`.
  have hx_not_intA : x ∉ interior A := by
    intro hx_intA
    -- Since `interior A ⊆ interior (closure A)`, this contradicts `hx.2`.
    have : x ∈ interior (closure A) := by
      have h_subset : interior A ⊆ interior (closure A) :=
        interior_subset_interior_closure
      exact h_subset hx_intA
    exact hx.2 this
  exact And.intro hx_closureA hx_not_intA