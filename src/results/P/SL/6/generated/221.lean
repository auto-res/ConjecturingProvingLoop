

theorem interior_closure_iInter_subset_iInter_interior_closure
    {X : Type*} [TopologicalSpace X] {ι : Sort*} {S : ι → Set X} :
    interior (closure (⋂ i, S i : Set X)) ⊆ ⋂ i, interior (closure (S i)) := by
  classical
  intro x hx
  -- For each index `i`, show that `x` belongs to `interior (closure (S i))`.
  have hx_i : ∀ i, x ∈ interior (closure (S i)) := by
    intro i
    -- `⋂ i, S i ⊆ S i`, hence their closures satisfy the same inclusion.
    have hSub : closure (⋂ j, S j : Set X) ⊆ closure (S i) := by
      apply closure_mono
      intro y hy
      exact (Set.mem_iInter.1 hy) i
    -- Monotonicity of `interior` turns this into an inclusion of interiors.
    have hIncl :
        interior (closure (⋂ j, S j : Set X))
          ⊆ interior (closure (S i)) :=
      interior_mono hSub
    exact hIncl hx
  -- Combine the pointwise memberships into one for the intersection.
  exact Set.mem_iInter.2 hx_i