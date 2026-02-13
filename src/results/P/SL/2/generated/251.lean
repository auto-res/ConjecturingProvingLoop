

theorem Topology.interior_iInter_subset_iInter_interior
    {X : Type*} [TopologicalSpace X] {ι : Type*} {s : ι → Set X} :
    interior (⋂ i, s i : Set X) ⊆ ⋂ i, interior (s i) := by
  intro x hx
  -- For each index `i`, we will show that `x ∈ interior (s i)`.
  have h : ∀ i, x ∈ interior (s i) := by
    intro i
    -- Since `⋂ j, s j ⊆ s i`, monotonicity of `interior` yields the claim.
    have hSub : (⋂ j, s j : Set X) ⊆ s i := by
      intro y hy
      exact (Set.mem_iInter.1 hy) i
    have hInt : interior (⋂ j, s j : Set X) ⊆ interior (s i) :=
      interior_mono hSub
    exact hInt hx
  -- Combine the pointwise facts into membership of the intersection.
  exact Set.mem_iInter.2 h