

theorem Topology.closure_interior_subset_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior A) ⊆ closure A := by
  -- `interior A` is contained in `A`.
  have h : interior A ⊆ (A : Set X) := interior_subset
  -- Taking closures preserves inclusion.
  exact closure_mono h