

theorem Topology.interior_iInter_subset
    {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} :
    interior (⋂ i, A i) ⊆ ⋂ i, interior (A i) := by
  intro x hx
  -- For each `i`, show `x ∈ interior (A i)`.
  have h_each : ∀ i, (x : X) ∈ interior (A i) := by
    intro i
    -- The intersection is contained in `A i`.
    have h_subset : (⋂ j, A j : Set X) ⊆ A i := by
      intro y hy
      exact (Set.mem_iInter.1 hy) i
    -- Monotonicity of `interior` gives the desired inclusion.
    have h_int_mono : interior (⋂ j, A j) ⊆ interior (A i) :=
      interior_mono h_subset
    exact h_int_mono hx
  -- Combine the pointwise facts into the intersection.
  exact Set.mem_iInter.2 h_each