

theorem Topology.closure_iInter_subset_iInter_closure
    {X : Type*} [TopologicalSpace X] {ι : Sort*} {𝒜 : ι → Set X} :
    closure (⋂ i, 𝒜 i) ⊆ ⋂ i, closure (𝒜 i) := by
  intro x hx
  -- For each `i`, `⋂ i, 𝒜 i ⊆ 𝒜 i`; taking closures preserves inclusion.
  have h_forall : ∀ i, x ∈ closure (𝒜 i) := by
    intro i
    have h_subset : (⋂ j, 𝒜 j : Set X) ⊆ 𝒜 i := by
      intro y hy
      exact (Set.mem_iInter.1 hy) i
    exact (closure_mono h_subset) hx
  exact Set.mem_iInter.2 h_forall