

theorem Topology.closure_diff_subset_closure {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure ((A \ B) : Set X) ⊆ closure (A : Set X) := by
  -- Since `A \ B ⊆ A`, the monotonicity of `closure` yields the desired inclusion.
  have hSub : ((A \ B) : Set X) ⊆ A := by
    intro x hx
    exact hx.1
  exact closure_mono hSub