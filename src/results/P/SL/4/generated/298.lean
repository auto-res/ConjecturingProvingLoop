

theorem closure_diff_subset_closure_left {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A \ B) ⊆ closure A := by
  -- The set difference `A \ B` is clearly contained in `A`.
  have h_sub : (A \ B : Set X) ⊆ A := by
    intro x hx
    exact hx.1
  -- Monotonicity of `closure` yields the desired inclusion.
  exact closure_mono h_sub