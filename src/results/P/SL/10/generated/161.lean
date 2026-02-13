

theorem Topology.interior_iInter_closure_subset {X : Type*} [TopologicalSpace X]
    {ι : Sort*} {A : ι → Set X} :
    interior (⋂ i, closure (A i)) ⊆ ⋂ i, interior (closure (A i)) := by
  intro x hx
  -- Show membership in each component of the intersection.
  have hx_i : ∀ i, x ∈ interior (closure (A i)) := by
    intro i
    -- The intersection is contained in each individual closure.
    have h_subset : (⋂ j, closure (A j)) ⊆ closure (A i) := by
      intro y hy
      exact (Set.mem_iInter.1 hy) i
    -- Pass to interiors via monotonicity.
    have h_int_subset :
        interior (⋂ j, closure (A j)) ⊆ interior (closure (A i)) :=
      interior_mono h_subset
    exact h_int_subset hx
  exact Set.mem_iInter.2 hx_i