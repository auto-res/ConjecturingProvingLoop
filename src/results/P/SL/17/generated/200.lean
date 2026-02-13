

theorem Topology.frontier_closure_subset_frontier
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    frontier (closure A) ⊆ frontier A := by
  intro x hx
  -- `hx` yields both `x ∈ closure (closure A)` and `x ∉ interior (closure A)`.
  have hx_closure : x ∈ closure A := by
    -- Simplify `closure (closure A)` to `closure A`.
    simpa [closure_closure] using hx.1
  have hx_not_intA : x ∉ interior A := by
    intro hx_intA
    -- `interior A ⊆ interior (closure A)`.
    have h_subset : interior A ⊆ interior (closure A) :=
      Topology.interior_subset_interior_closure (A := A)
    have : x ∈ interior (closure A) := h_subset hx_intA
    exact hx.2 this
  -- Combine the two facts to obtain `x ∈ frontier A`.
  exact And.intro hx_closure hx_not_intA