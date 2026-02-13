

theorem Topology.interior_iInter_subset_iInter_interior
    {ι X : Type*} [TopologicalSpace X] {A : ι → Set X} :
    interior (⋂ i, A i : Set X) ⊆ ⋂ i, interior (A i) := by
  intro x hx
  -- For each index `i`, `(⋂ i, A i) ⊆ A i`.
  have hxi : ∀ i, x ∈ interior (A i) := by
    intro i
    have h_subset : (⋂ j, A j : Set X) ⊆ A i := by
      intro y hy
      exact (Set.mem_iInter.1 hy) i
    exact (interior_mono h_subset) hx
  exact Set.mem_iInter.2 hxi