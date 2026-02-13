

theorem closure_diff_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure ((A \ B) : Set X) ⊆ closure A := by
  -- Since `A \ B ⊆ A`, the monotonicity of `closure` gives the result.
  exact closure_mono (by
    intro x hx
    exact hx.1)