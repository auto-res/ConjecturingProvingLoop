

theorem Topology.interior_diff_subset_left
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (A \ B) ⊆ interior A := by
  -- The set difference `A \ B` is contained in `A`.
  have hsubset : (A \ B : Set X) ⊆ A := by
    intro x hx
    exact hx.1
  -- Apply monotonicity of `interior` to obtain the desired inclusion.
  exact interior_mono hsubset