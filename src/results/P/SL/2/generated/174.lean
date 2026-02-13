

theorem Topology.closure_interior_iInter_subset_iInter_closure_interior
    {X : Type*} [TopologicalSpace X] {ι : Type*} {s : ι → Set X} :
    closure (interior (⋂ i, s i : Set X)) ⊆ ⋂ i, closure (interior (s i)) := by
  intro x hx
  -- For each index `i`, we will show `x ∈ closure (interior (s i))`.
  have hx₀ : x ∈ closure (interior (⋂ i, s i : Set X)) := hx
  have hxi : ∀ i, x ∈ closure (interior (s i)) := by
    intro i
    -- `interior (⋂ i, s i)` is contained in `interior (s i)`
    have hsub :
        (interior (⋂ j, s j : Set X) : Set X) ⊆ interior (s i) := by
      -- Since `⋂ j, s j ⊆ s i`, monotonicity of `interior` gives the claim.
      have hSup : (⋂ j, s j : Set X) ⊆ s i := by
        intro y hy
        exact (Set.mem_iInter.1 hy) i
      exact interior_mono hSup
    -- Taking closures preserves inclusions.
    have hcl :
        closure (interior (⋂ j, s j : Set X)) ⊆ closure (interior (s i)) :=
      closure_mono hsub
    exact hcl hx₀
  -- Combine the pointwise facts into membership in the intersection.
  exact Set.mem_iInter.2 hxi