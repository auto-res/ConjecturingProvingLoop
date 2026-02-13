

theorem interior_iInter_subset_iInter_interior
    {X ι : Type*} [TopologicalSpace X] {A : ι → Set X} :
    interior (⋂ i, A i) ⊆ ⋂ i, interior (A i) := by
  intro x hx
  -- For each index `i`, show `x ∈ interior (A i)`.
  have hx_all : ∀ i, x ∈ interior (A i) := by
    intro i
    -- The intersection is contained in each `A i`.
    have hsubset : (⋂ j, A j) ⊆ A i :=
      Set.iInter_subset (fun j => A j) i
    -- Monotonicity of `interior` transfers membership.
    exact (interior_mono hsubset) hx
  -- Aggregate the memberships into the intersection of interiors.
  exact Set.mem_iInter.2 hx_all