

theorem interior_iInter_closure_subset_iInter_interior_closure
    {X : Type*} [TopologicalSpace X] {ι : Sort*} {S : ι → Set X} :
    interior (⋂ i, closure (S i) : Set X) ⊆ ⋂ i, interior (closure (S i)) := by
  intro x hx
  -- For each index `i`, we will show `x ∈ interior (closure (S i))`.
  have hx_i : ∀ i, x ∈ interior (closure (S i)) := by
    intro i
    -- The intersection is contained in each component `closure (S i)`.
    have hSub : (⋂ j, closure (S j) : Set X) ⊆ closure (S i) := by
      intro y hy
      exact (Set.mem_iInter.1 hy) i
    -- Monotonicity of `interior` upgrades the inclusion.
    exact (interior_mono hSub) hx
  -- Combine the pointwise facts into membership in the intersection.
  exact Set.mem_iInter.2 hx_i