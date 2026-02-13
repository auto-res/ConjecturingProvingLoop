

theorem Topology.closure_inter_interior_subset_left {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure ((A ∩ interior B) : Set X) ⊆ closure (A : Set X) := by
  -- Since `A ∩ interior B ⊆ A`, monotonicity of `closure` gives the claim.
  have h_subset : ((A ∩ interior B) : Set X) ⊆ A := by
    intro x hx
    exact hx.1
  exact closure_mono h_subset