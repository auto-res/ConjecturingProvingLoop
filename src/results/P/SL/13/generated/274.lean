

theorem Topology.closure_diff_subset_closure_left {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure ((A \ B) : Set X) ⊆ closure (A : Set X) := by
  -- Since `A \ B ⊆ A`, monotonicity of `closure` yields the desired inclusion.
  exact closure_mono (by
    intro x hx
    exact hx.1)