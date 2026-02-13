

theorem Topology.closure_diff_subset_closure {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (A \ B : Set X) ⊆ closure A := by
  -- `A \ B` is contained in `A`, so the monotonicity of `closure` gives the result.
  exact closure_mono (by
    intro x hx
    exact hx.1)