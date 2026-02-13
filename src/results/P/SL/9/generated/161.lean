

theorem Topology.interior_iInter_subset_iInter_interior
    {X : Type*} [TopologicalSpace X] {ι : Sort*} {𝒜 : ι → Set X} :
    interior (⋂ i, 𝒜 i) ⊆ ⋂ i, interior (𝒜 i) := by
  intro x hx
  have h_forall : ∀ i, x ∈ interior (𝒜 i) := by
    intro i
    -- Since `⋂ j, 𝒜 j ⊆ 𝒜 i`, monotonicity of `interior` yields the result.
    have h_subset : (⋂ j, 𝒜 j : Set X) ⊆ 𝒜 i := by
      intro y hy
      exact (Set.mem_iInter.1 hy) i
    have h_int_subset : interior (⋂ j, 𝒜 j) ⊆ interior (𝒜 i) :=
      interior_mono h_subset
    exact h_int_subset hx
  exact Set.mem_iInter.2 h_forall