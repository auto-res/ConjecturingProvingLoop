

theorem Topology.interior_diff_subset_left {X : Type*} [TopologicalSpace X]
    (A B : Set X) : interior (A \ B : Set X) ⊆ interior A := by
  intro x hx
  -- Since `A \ B ⊆ A`, monotonicity of `interior` yields the claim.
  have h_subset : (A \ B : Set X) ⊆ A := by
    intro y hy
    exact hy.1
  exact (interior_mono h_subset) hx