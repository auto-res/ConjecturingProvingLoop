

theorem Topology.closure_interior_iInter_subset {X : Type*} [TopologicalSpace X]
    {ι : Sort*} {A : ι → Set X} :
    closure (interior (⋂ i, A i)) ⊆ ⋂ i, closure (interior (A i)) := by
  intro x hx
  -- We will show `x` lies in each `closure (interior (A i))`.
  have hxi : ∀ i, x ∈ closure (interior (A i)) := by
    intro i
    -- First observe the basic inclusion `(⋂ j, A j) ⊆ A i`.
    have h_subset₁ : (⋂ j, A j) ⊆ A i := by
      intro y hy
      exact (Set.mem_iInter.1 hy) i
    -- Pass to interiors using monotonicity.
    have h_subset₂ : interior (⋂ j, A j) ⊆ interior (A i) :=
      interior_mono h_subset₁
    -- Finally, pass to closures.
    exact (closure_mono h_subset₂) hx
  -- Package the pointwise memberships into an intersection.
  exact Set.mem_iInter.2 hxi