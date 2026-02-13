

theorem Topology.closure_interior_subset_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) : closure (interior A) ⊆ (A : Set X) := by
  -- `interior A` is contained in `A`.
  have hsubset : (interior A : Set X) ⊆ A := interior_subset
  -- Taking closures preserves inclusion.
  have hclosure : closure (interior A) ⊆ closure A := closure_mono hsubset
  -- Since `A` is closed, its closure is itself.
  simpa [hA.closure_eq] using hclosure