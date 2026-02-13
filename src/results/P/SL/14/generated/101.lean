

theorem Topology.interiorClosure_iInter_subset
    {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} :
    interior (closure (⋂ i, A i)) ⊆ ⋂ i, interior (closure (A i)) := by
  intro x hx
  -- For each `i`, show `x ∈ interior (closure (A i))`.
  have h_each : ∀ i, (x : X) ∈ interior (closure (A i)) := by
    intro i
    -- The intersection is contained in `A i`.
    have h_subset : (⋂ j, A j : Set X) ⊆ A i := by
      intro y hy
      exact (Set.mem_iInter.1 hy) i
    -- Apply monotonicity of `closure` and `interior`.
    have h_closure_mono : closure (⋂ j, A j) ⊆ closure (A i) :=
      closure_mono h_subset
    have h_int_mono : interior (closure (⋂ j, A j)) ⊆
        interior (closure (A i)) := interior_mono h_closure_mono
    exact h_int_mono hx
  exact Set.mem_iInter.2 h_each