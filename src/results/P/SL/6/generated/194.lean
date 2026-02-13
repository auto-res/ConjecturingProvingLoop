

theorem interior_diff_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior ((A \ B) : Set X) ⊆ interior A := by
  -- Since `A \ B ⊆ A`, monotonicity of `interior` yields the desired inclusion.
  have hSub : (A \ B : Set X) ⊆ A := by
    intro x hx
    exact hx.1
  exact interior_mono hSub