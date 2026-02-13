

theorem Topology.closure_interior_subset_of_isClosed {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : IsClosed (A : Set X)) :
    closure (interior (A : Set X)) ⊆ A := by
  -- First, `closure (interior A)` is contained in `closure A` by monotonicity.
  have h_sub : closure (interior (A : Set X)) ⊆ closure A :=
    closure_mono (interior_subset : (interior (A : Set X)) ⊆ A)
  -- Since `A` is closed, `closure A = A`; rewrite and finish.
  simpa [hA.closure_eq] using h_sub