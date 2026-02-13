

theorem Topology.interior_iInter_subset {X : Type*} [TopologicalSpace X]
    {ι : Sort*} {A : ι → Set X} :
    interior (⋂ i, A i) ⊆ ⋂ i, interior (A i) := by
  intro x hx
  -- Show `x` belongs to each `interior (A i)`.
  have hxi : ∀ i, x ∈ interior (A i) := by
    intro i
    -- The intersection is contained in each component `A i`.
    have h_subset : (⋂ j, A j) ⊆ A i := by
      intro y hy
      exact (Set.mem_iInter.1 hy) i
    -- Pass to interiors using monotonicity.
    have h_int_subset : interior (⋂ j, A j) ⊆ interior (A i) :=
      interior_mono h_subset
    exact h_int_subset hx
  exact Set.mem_iInter.2 hxi