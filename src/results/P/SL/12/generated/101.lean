

theorem Topology.closure_interior_iInter_subset
    {X ι : Type*} [TopologicalSpace X] (A : ι → Set X) :
    closure (interior (⋂ i, A i : Set X)) ⊆ ⋂ i, closure (interior (A i)) := by
  intro x hx
  -- We will show that `x` belongs to each `closure (interior (A i))`.
  have hx_each : ∀ i, x ∈ closure (interior (A i)) := by
    intro i
    -- First, note that `⋂ i, A i ⊆ A i`.
    have h_subset : (⋂ j, A j : Set X) ⊆ A i := by
      intro y hy
      -- Expand the intersection membership.
      have h_all : ∀ j, y ∈ A j := (Set.mem_iInter.mp hy)
      exact h_all i
    -- Monotonicity of `interior` gives the corresponding inclusion for interiors.
    have h_int :
        (interior (⋂ j, A j : Set X) : Set X) ⊆ interior (A i) :=
      interior_mono h_subset
    -- Taking closures preserves inclusion.
    have h_closure :
        closure (interior (⋂ j, A j : Set X)) ⊆ closure (interior (A i)) :=
      closure_mono h_int
    -- Apply the inclusion to the hypothesis.
    exact h_closure hx
  -- Combine the pointwise memberships into one for the intersection.
  exact (Set.mem_iInter.2 hx_each)