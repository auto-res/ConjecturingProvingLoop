

theorem Topology.closure_diff_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A \ B : Set X) ⊆ closure A := by
  -- The set `A \ B` is contained in `A`.
  have h_subset : (A \ B : Set X) ⊆ A := by
    intro x hx
    exact hx.1
  -- Monotonicity of `closure` yields the desired inclusion.
  exact closure_mono h_subset