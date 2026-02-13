

theorem Topology.interior_closure_iInter_subset_iInter_interior_closure
    {ι X : Type*} [TopologicalSpace X] {A : ι → Set X} :
    interior (closure (⋂ i, A i : Set X)) ⊆ ⋂ i, interior (closure (A i)) := by
  intro x hx
  -- Show that `x` belongs to `interior (closure (A i))` for each `i`.
  have hx_i : ∀ i, x ∈ interior (closure (A i)) := by
    intro i
    -- Because `(⋂ i, A i) ⊆ A i`, we get the inclusion on closures.
    have h_subset : closure (⋂ j, A j : Set X) ⊆ closure (A i) := by
      apply closure_mono
      intro y hy
      exact (Set.mem_iInter.1 hy) i
    -- Use monotonicity of `interior` to transport `hx`.
    exact (interior_mono h_subset) hx
  -- Re-assemble the pointwise membership into an intersection.
  exact Set.mem_iInter.2 hx_i