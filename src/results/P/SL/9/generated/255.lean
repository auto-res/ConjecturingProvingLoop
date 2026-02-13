

theorem Topology.frontier_interior_subset_frontier
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    frontier (interior (A : Set X)) ⊆ frontier A := by
  intro x hx
  -- Decompose membership in the frontier of `interior A`.
  rcases hx with ⟨hx_cl_int, hx_not_int_int⟩
  -- `closure (interior A)` is contained in `closure A`.
  have hx_clA : x ∈ closure (A : Set X) :=
    (closure_mono (interior_subset : interior A ⊆ A)) hx_cl_int
  -- `interior (interior A)` coincides with `interior A`.
  have hx_not_intA : x ∉ interior (A : Set X) := by
    simpa [interior_interior] using hx_not_int_int
  exact ⟨hx_clA, hx_not_intA⟩