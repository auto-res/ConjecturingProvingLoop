

theorem Topology.closure_interior_iInter_subset_iInter_closure_interior
    {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} :
    closure (interior (Set.iInter A)) ⊆ (Set.iInter fun i => closure (interior (A i))) := by
  intro x hx
  -- For every index `i`, show that `x` lies in `closure (interior (A i))`.
  have hx_i : ∀ i, x ∈ closure (interior (A i)) := by
    intro i
    -- `interior` is monotone, and `⋂ i, A i` is contained in each `A i`.
    have h_subset : interior (Set.iInter A) ⊆ interior (A i) :=
      interior_mono (Set.iInter_subset A i)
    -- Taking closures preserves inclusions.
    have h_closure : closure (interior (Set.iInter A)) ⊆
        closure (interior (A i)) := closure_mono h_subset
    exact h_closure hx
  -- Assemble the memberships into the required intersection.
  exact Set.mem_iInter.2 hx_i