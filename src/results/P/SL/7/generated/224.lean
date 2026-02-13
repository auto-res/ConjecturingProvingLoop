

theorem Topology.interior_iInter_subset {X : Type*} [TopologicalSpace X]
    {ι : Sort _} {F : ι → Set X} :
    interior (⋂ i, F i) ⊆ ⋂ i, interior (F i) := by
  intro x hx
  -- For each index `i`, show `x ∈ interior (F i)`.
  have h : ∀ i, x ∈ interior (F i) := by
    intro i
    -- The set `⋂ i, F i` is contained in `F i`.
    have hSub : (⋂ j, F j : Set X) ⊆ F i := by
      intro y hy
      exact (Set.mem_iInter.1 hy) i
    -- Monotonicity of `interior` transports the inclusion.
    have hIncl : interior (⋂ j, F j) ⊆ interior (F i) :=
      interior_mono hSub
    exact hIncl hx
  -- Assemble the pointwise memberships into one for the intersection.
  exact Set.mem_iInter.2 h