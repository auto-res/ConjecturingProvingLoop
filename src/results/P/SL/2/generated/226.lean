

theorem Topology.frontier_interior_subset_frontier {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    frontier (interior (A : Set X)) ⊆ frontier A := by
  intro x hx
  -- Unpack the definition of the frontier of `interior A`.
  rcases hx with ⟨hx_closureInt, hx_not_intInt⟩
  -- `closure (interior A)` is contained in `closure A`.
  have hsubset : (closure (interior (A : Set X)) : Set X) ⊆ closure A :=
    Topology.closure_interior_subset_closure (A := A)
  -- Assemble the two conditions defining `x ∈ frontier A`.
  refine And.intro (hsubset hx_closureInt) ?_
  -- Rewrite `x ∉ interior (interior A)` as `x ∉ interior A`.
  simpa [interior_interior] using hx_not_intInt