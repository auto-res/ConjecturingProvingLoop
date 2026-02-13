

theorem Topology.interior_diff_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (A \ B : Set X) ⊆ interior A := by
  -- `A \ B` is contained in `A`.
  have h_subset : (A \ B : Set X) ⊆ A := by
    intro x hx
    exact hx.1
  -- Apply monotonicity of `interior`.
  exact interior_mono h_subset