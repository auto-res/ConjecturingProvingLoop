

theorem Topology.closure_diff_interior_subset_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    closure (A \ interior A) ⊆ closure A := by
  -- The set difference `A \ interior A` is clearly contained in `A`.
  have hSub : (A \ interior A : Set X) ⊆ A := by
    intro x hx
    exact hx.1
  -- Taking closures preserves inclusions.
  exact closure_mono hSub