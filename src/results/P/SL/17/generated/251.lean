

theorem Topology.interior_iInter_subset_iInter_interior
    {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} :
    interior (Set.iInter A) ⊆ Set.iInter (fun i => interior (A i)) := by
  intro x hx
  -- For every index `i`, derive `x ∈ interior (A i)`.
  have hxi : ∀ i, x ∈ interior (A i) := by
    intro i
    -- `⋂ i, A i ⊆ A i`
    have h_subset : (Set.iInter A) ⊆ A i := by
      intro y hy
      exact (Set.mem_iInter.1 hy) i
    -- Monotonicity of `interior` yields the desired inclusion.
    have h_mono : interior (Set.iInter A) ⊆ interior (A i) :=
      interior_mono h_subset
    exact h_mono hx
  -- Assemble the memberships into the required intersection.
  exact Set.mem_iInter.2 hxi