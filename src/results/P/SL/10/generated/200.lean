

theorem Topology.closure_iInter_subset
    {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} :
    closure (⋂ i, A i) ⊆ ⋂ i, closure (A i) := by
  intro x hx
  -- Show that `x` belongs to the closure of each `A i`.
  have hx_i : ∀ i, x ∈ closure (A i) := by
    intro i
    -- The intersection is contained in each component `A i`.
    have h_subset : (⋂ j, A j) ⊆ A i := by
      intro y hy
      exact (Set.mem_iInter.1 hy) i
    -- Taking closures preserves inclusions.
    have h_closure : closure (⋂ j, A j) ⊆ closure (A i) :=
      closure_mono h_subset
    exact h_closure hx
  -- Package the pointwise memberships into an intersection.
  exact Set.mem_iInter.2 hx_i