

theorem Topology.interior_iInter_subset
    {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} :
    interior (⋂ i, A i) ⊆ ⋂ i, interior (A i) := by
  intro x hx
  -- We show that `x` belongs to the interior of each `A i`.
  have h : ∀ i, x ∈ interior (A i) := by
    intro i
    -- Since `⋂ i, A i ⊆ A i`, monotonicity of `interior` yields the claim.
    have hsubset : (⋂ j, A j : Set X) ⊆ A i := Set.iInter_subset _ i
    have hInt : interior (⋂ j, A j) ⊆ interior (A i) := interior_mono hsubset
    exact hInt hx
  -- Combine the individual memberships into the intersection.
  exact Set.mem_iInter.2 h