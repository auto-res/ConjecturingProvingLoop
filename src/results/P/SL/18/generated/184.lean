

theorem closure_diff_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A \ B : Set X) ⊆ closure (A : Set X) := by
  -- The set difference `A \ B` is contained in `A`.
  have hSub : (A \ B : Set X) ⊆ A := Set.diff_subset
  -- Use the monotonicity of `closure` to lift the inclusion.
  exact closure_mono hSub