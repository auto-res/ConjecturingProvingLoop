

theorem interior_iInter_subset_interiors
    {ι : Sort _} {X : Type _} [TopologicalSpace X] (A : ι → Set X) :
    interior (⋂ i, A i : Set X) ⊆ ⋂ i, interior (A i) := by
  intro x hx
  -- For each `i`, `x` lies in `interior (A i)`.
  have hx_i : ∀ i, x ∈ interior (A i) := by
    intro i
    -- The intersection is contained in each component.
    have hSub : (⋂ j, A j : Set X) ⊆ A i := by
      intro y hy
      exact (Set.mem_iInter.1 hy) i
    -- Monotonicity of `interior` gives the desired inclusion.
    have hInt : interior (⋂ j, A j : Set X) ⊆ interior (A i) :=
      interior_mono hSub
    exact hInt hx
  -- Assemble the pointwise condition into membership in the intersection.
  exact Set.mem_iInter.2 hx_i