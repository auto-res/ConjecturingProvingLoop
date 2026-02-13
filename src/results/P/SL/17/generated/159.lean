

theorem Topology.interior_diff_subset_interior_left
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (A \ B) ⊆ interior A := by
  -- Since `A \ B ⊆ A`, apply the monotonicity of `interior`.
  have h_subset : (A \ B : Set X) ⊆ A := by
    intro x hx
    exact hx.1
  exact interior_mono h_subset