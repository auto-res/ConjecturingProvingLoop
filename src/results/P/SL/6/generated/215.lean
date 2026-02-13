

theorem closure_iInter_subset_iInter_closure
    {X : Type*} [TopologicalSpace X] {ι : Sort*} {S : ι → Set X} :
    closure (⋂ i, S i : Set X) ⊆ (⋂ i, closure (S i) : Set X) := by
  intro x hx
  -- For each index `i`, derive `x ∈ closure (S i)`.
  have hx_i : ∀ i, x ∈ closure (S i) := by
    intro i
    -- The intersection is contained in each component `S i`.
    have hSub : (⋂ j, S j : Set X) ⊆ S i := by
      intro y hy
      exact (Set.mem_iInter.1 hy) i
    -- Monotonicity of `closure` lifts this inclusion.
    have hIncl : closure (⋂ j, S j : Set X) ⊆ closure (S i) :=
      closure_mono hSub
    exact hIncl hx
  -- Combine the individual memberships into one for the intersection of closures.
  exact (Set.mem_iInter.2 hx_i)