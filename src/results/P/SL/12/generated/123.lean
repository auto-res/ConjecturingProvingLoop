

theorem Topology.interior_iInter_subset_iInter_interior
    {X ι : Type*} [TopologicalSpace X] (A : ι → Set X) :
    interior (⋂ i, A i : Set X) ⊆ ⋂ i, interior (A i) := by
  intro x hx
  -- Show that `x` belongs to each `interior (A i)`.
  have hx_each : ∀ i, x ∈ interior (A i) := by
    intro i
    -- Since `⋂ i, A i ⊆ A i`, monotonicity of `interior` yields the result.
    have h_subset : (⋂ j, A j : Set X) ⊆ A i := by
      intro y hy
      exact (Set.mem_iInter.1 hy) i
    have h_int : interior (⋂ j, A j : Set X) ⊆ interior (A i) :=
      interior_mono h_subset
    exact h_int hx
  -- Combine the pointwise facts into a membership of the intersection.
  exact (Set.mem_iInter.2 hx_each)