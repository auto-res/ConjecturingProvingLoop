

theorem Topology.closure_diff_subset_closure {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (A \ B : Set X) ⊆ closure A := by
  -- The set difference `A \ B` is contained in `A`.
  have h_subset : (A \ B : Set X) ⊆ A := Set.diff_subset
  -- Monotonicity of `closure` yields the desired inclusion.
  exact closure_mono h_subset