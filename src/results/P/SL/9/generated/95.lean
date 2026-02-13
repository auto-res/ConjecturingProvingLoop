

theorem Topology.interiorClosure_iInter_subset {X : Type*} [TopologicalSpace X]
    {ι : Sort*} {𝒜 : ι → Set X} :
    interior (closure (⋂ i, 𝒜 i)) ⊆ ⋂ i, interior (closure (𝒜 i)) := by
  intro x hx
  -- Show that `x` lies in every `interior (closure (𝒜 i))`.
  have h_forall : ∀ i, x ∈ interior (closure (𝒜 i)) := by
    intro i
    -- Since `⋂ j, 𝒜 j ⊆ 𝒜 i`, the same holds for their closures.
    have h_subset : closure (⋂ j, 𝒜 j) ⊆ closure (𝒜 i) := by
      have h_inter_subset : (⋂ j, 𝒜 j : Set X) ⊆ 𝒜 i := by
        intro y hy
        exact (Set.mem_iInter.1 hy) i
      exact closure_mono h_inter_subset
    -- Apply monotonicity of `interior`.
    exact (interior_mono h_subset) hx
  exact Set.mem_iInter.2 h_forall