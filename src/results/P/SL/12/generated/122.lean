

theorem Topology.interior_iInter_closure_subset_iInter_interior_closure
    {X ι : Type*} [TopologicalSpace X] (A : ι → Set X) :
    interior (⋂ i, closure (A i) : Set X) ⊆ ⋂ i, interior (closure (A i)) := by
  intro x hx
  -- For each index `i`, we show `x ∈ interior (closure (A i))`.
  have h_i : ∀ i, x ∈ interior (closure (A i)) := by
    intro i
    -- `⋂ i, closure (A i) ⊆ closure (A i)`.
    have h_subset :
        (⋂ j, closure (A j) : Set X) ⊆ closure (A i) := by
      intro y hy
      exact (Set.mem_iInter.1 hy) i
    -- Apply monotonicity of `interior`.
    have h_int :
        interior (⋂ j, closure (A j) : Set X) ⊆ interior (closure (A i)) :=
      interior_mono h_subset
    exact h_int hx
  -- Combine the pointwise statements into one for the intersection.
  exact (Set.mem_iInter.2 h_i)