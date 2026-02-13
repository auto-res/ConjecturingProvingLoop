

theorem Topology.closure_iInter_subset
    {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} :
    closure (⋂ i, A i) ⊆ ⋂ i, closure (A i) := by
  intro x hx
  -- For each `i`, `(⋂ j, A j) ⊆ A i`, so their closures satisfy the same inclusion.
  have h : ∀ i, x ∈ closure (A i) := by
    intro i
    have hsubset : (⋂ j, A j : Set X) ⊆ A i := by
      exact Set.iInter_subset _ i
    have : closure (⋂ j, A j) ⊆ closure (A i) := closure_mono hsubset
    exact this hx
  -- Combine the individual memberships into one for the intersection of closures.
  exact Set.mem_iInter.2 h