

theorem Topology.closureInterior_iInter_subset
    {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} :
    closure (interior (⋂ i, A i)) ⊆ ⋂ i, closure (interior (A i)) := by
  intro x hx
  -- For each `i`, we will show `x ∈ closure (interior (A i))`.
  have h_each : ∀ i, (x : X) ∈ closure (interior (A i)) := by
    intro i
    -- `interior (⋂ i, A i)` is contained in `interior (A i)`.
    have h_int_subset : interior (⋂ j, A j) ⊆ interior (A i) := by
      have h_subset : (⋂ j, A j : Set X) ⊆ A i := by
        intro y hy
        exact (Set.mem_iInter.1 hy) i
      exact interior_mono h_subset
    -- Taking closures preserves this inclusion.
    have h_closure_subset :
        closure (interior (⋂ j, A j)) ⊆ closure (interior (A i)) :=
      closure_mono h_int_subset
    exact h_closure_subset hx
  -- Conclude that `x` lies in the intersection of all these closures.
  exact Set.mem_iInter.2 h_each