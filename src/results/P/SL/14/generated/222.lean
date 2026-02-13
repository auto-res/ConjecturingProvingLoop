

theorem Topology.closure_sInter_subset
    {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} :
    closure (⋂₀ 𝒜 : Set X) ⊆ ⋂₀ ((fun S : Set X => closure S) '' 𝒜) := by
  intro x hx
  apply Set.mem_sInter.2
  intro S hS
  rcases hS with ⟨T, hT𝒜, rfl⟩
  -- Since `⋂₀ 𝒜 ⊆ T`, taking closures preserves the inclusion.
  have h_subset : (⋂₀ 𝒜 : Set X) ⊆ T := by
    intro y hy
    exact (Set.mem_sInter.1 hy) T hT𝒜
  have h_closure_subset :
      closure (⋂₀ 𝒜 : Set X) ⊆ closure T := closure_mono h_subset
  exact h_closure_subset hx