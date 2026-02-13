

theorem Topology.closure_iInter_subset_iInter_closure
    {X ι : Type*} [TopologicalSpace X] (A : ι → Set X) :
    closure (⋂ i, A i : Set X) ⊆ ⋂ i, closure (A i) := by
  intro x hx
  -- For each index `i`, we show that `x ∈ closure (A i)`.
  have h_i : ∀ i, x ∈ closure (A i) := by
    intro i
    -- The intersection is contained in each `A i`.
    have h_subset : (⋂ j, A j : Set X) ⊆ A i := by
      intro y hy
      exact (Set.mem_iInter.1 hy) i
    -- Monotonicity of `closure` gives the desired inclusion.
    have h_closure :
        closure (⋂ j, A j : Set X) ⊆ closure (A i) :=
      closure_mono h_subset
    exact h_closure hx
  -- Combine the pointwise facts into the desired membership.
  exact (Set.mem_iInter.2 h_i)