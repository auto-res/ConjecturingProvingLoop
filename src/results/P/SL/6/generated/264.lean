

theorem interior_iInter_subset_iInter_interior
    {X : Type*} [TopologicalSpace X] {ι : Sort*} {S : ι → Set X} :
    interior (⋂ i, S i : Set X) ⊆ ⋂ i, interior (S i) := by
  intro x hx
  -- For each index `i`, show `x ∈ interior (S i)`.
  have hx_i : ∀ i, x ∈ interior (S i) := by
    intro i
    -- The intersection is contained in `S i`.
    have hSub : (⋂ j, S j : Set X) ⊆ S i := by
      intro y hy
      exact (Set.mem_iInter.1 hy) i
    -- Apply monotonicity of `interior`.
    have hIncl : interior (⋂ j, S j : Set X) ⊆ interior (S i) :=
      interior_mono hSub
    exact hIncl hx
  -- Combine the pointwise fact into membership in the intersection of interiors.
  exact Set.mem_iInter.2 hx_i