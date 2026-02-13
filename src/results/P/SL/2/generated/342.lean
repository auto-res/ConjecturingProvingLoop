

theorem Topology.closure_interior_diff_subset_frontier
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior A) \ (A : Set X) ⊆ frontier (A : Set X) := by
  intro x hx
  -- `hx` gives the facts that `x ∈ closure (interior A)` and `x ∉ A`.
  have hx_cl_int : x ∈ closure (interior A) := hx.1
  have hx_not_A  : x ∉ (A : Set X)     := hx.2
  -- Since `interior A ⊆ A ⊆ closure A`, we have
  -- `closure (interior A) ⊆ closure A`; hence `x ∈ closure A`.
  have hsubset : (closure (interior A) : Set X) ⊆ closure (A : Set X) :=
    Topology.closure_interior_subset_closure (A := A)
  have hx_cl_A : x ∈ closure (A : Set X) := hsubset hx_cl_int
  -- To be in the frontier of `A`, we also need `x ∉ interior A`.
  have hx_not_int : x ∉ interior (A : Set X) := by
    intro hx_int
    exact hx_not_A (interior_subset hx_int)
  -- Assemble the two conditions defining the frontier.
  exact And.intro hx_cl_A hx_not_int