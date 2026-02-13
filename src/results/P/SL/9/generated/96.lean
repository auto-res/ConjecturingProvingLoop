

theorem Topology.closureInterior_iInter_subset
    {X : Type*} [TopologicalSpace X] {ι : Sort*} {𝒜 : ι → Set X} :
    closure (interior (⋂ i, 𝒜 i)) ⊆ ⋂ i, closure (interior (𝒜 i)) := by
  intro x hx
  -- Show that `x` lies in every `closure (interior (𝒜 i))`.
  have h_forall : ∀ i, x ∈ closure (interior (𝒜 i)) := by
    intro i
    -- Since `⋂ j, 𝒜 j ⊆ 𝒜 i`, the same holds for their interiors.
    have h_subset : interior (⋂ j, 𝒜 j) ⊆ interior (𝒜 i) := by
      -- The intersection is contained in each component.
      have h_set : (⋂ j, 𝒜 j : Set X) ⊆ 𝒜 i := by
        intro y hy
        exact (Set.mem_iInter.1 hy) i
      exact interior_mono h_set
    -- Taking closures preserves inclusion.
    have h_closure : closure (interior (⋂ j, 𝒜 j)) ⊆
        closure (interior (𝒜 i)) := closure_mono h_subset
    exact h_closure hx
  exact Set.mem_iInter.2 h_forall