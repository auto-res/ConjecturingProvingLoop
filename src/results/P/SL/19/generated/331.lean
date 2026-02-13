

theorem Topology.closure_frontier_subset_of_isClosed {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : IsClosed A) :
    closure (frontier A) ⊆ A := by
  -- First, we know the frontier itself is contained in `A`.
  have hSub : frontier A ⊆ A :=
    Topology.frontier_subset_of_isClosed (A := A) hA
  -- Taking closures preserves inclusions.
  have hClosSub : closure (frontier A) ⊆ closure A :=
    closure_mono hSub
  -- Since `A` is closed, its closure is itself.
  simpa [hA.closure_eq] using hClosSub