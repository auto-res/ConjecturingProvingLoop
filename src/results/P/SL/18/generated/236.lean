

theorem closure_iInter_subset
    {ι : Sort _} {X : Type _} [TopologicalSpace X] (A : ι → Set X) :
    closure (⋂ i, A i : Set X) ⊆ ⋂ i, closure (A i) := by
  intro x hx
  -- For each index `i`, show that `x ∈ closure (A i)`.
  have hxi : ∀ i, x ∈ closure (A i) := by
    intro i
    -- The intersection is contained in each component.
    have hSub : (⋂ j, A j : Set X) ⊆ A i := by
      intro y hy
      exact (Set.mem_iInter.1 hy) i
    -- Taking closures preserves inclusions.
    have hClos : closure (⋂ j, A j : Set X) ⊆ closure (A i) :=
      closure_mono hSub
    exact hClos hx
  -- Assemble the pointwise condition into membership in the intersection.
  exact Set.mem_iInter.2 hxi