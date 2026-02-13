

theorem Topology.interiorClosure_iInter_subset
    {X : Type*} [TopologicalSpace X] {ι : Sort _} {F : ι → Set X} :
    interior (closure (⋂ i, F i)) ⊆ ⋂ i, interior (closure (F i)) := by
  intro x hx
  -- We will show that `x` belongs to each component of the intersection.
  have h : ∀ i, x ∈ interior (closure (F i)) := by
    intro i
    -- Use monotonicity of `closure` and `interior` stemming from
    -- the inclusion `⋂ i, F i ⊆ F i`.
    have hSub : interior (closure (⋂ j, F j)) ⊆ interior (closure (F i)) := by
      apply interior_mono
      have h₀ : (⋂ j, F j : Set X) ⊆ F i := by
        intro y hy
        exact (Set.mem_iInter.1 hy) i
      exact closure_mono h₀
    exact hSub hx
  -- Assemble the pointwise memberships into one for the intersection.
  exact Set.mem_iInter.2 h