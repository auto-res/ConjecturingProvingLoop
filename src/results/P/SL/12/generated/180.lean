

theorem Topology.closure_iInter_interior_subset_iInter_closure_interior
    {X ι : Type*} [TopologicalSpace X] (A : ι → Set X) :
    closure (⋂ i, interior (A i) : Set X) ⊆ ⋂ i, closure (interior (A i)) := by
  intro x hx
  -- Show that `x` belongs to each `closure (interior (A i))`.
  have hx_i : ∀ i, x ∈ closure (interior (A i)) := by
    intro i
    -- `⋂ i, interior (A i) ⊆ interior (A i)`.
    have h_subset : (⋂ j, interior (A j) : Set X) ⊆ interior (A i) := by
      intro y hy
      exact (Set.mem_iInter.1 hy) i
    -- Apply monotonicity of `closure`.
    have h_closure :
        closure (⋂ j, interior (A j) : Set X) ⊆ closure (interior (A i)) :=
      closure_mono h_subset
    exact h_closure hx
  -- Combine the pointwise memberships into the intersection.
  exact (Set.mem_iInter.2 hx_i)