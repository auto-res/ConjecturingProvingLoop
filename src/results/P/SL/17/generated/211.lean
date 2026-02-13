

theorem Topology.closure_interior_subset_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) :
    closure (interior A) ⊆ A := by
  -- First, by monotonicity of `closure`, we have
  -- `closure (interior A) ⊆ closure A`.
  have h : closure (interior A) ⊆ closure A :=
    closure_mono (interior_subset : interior A ⊆ A)
  -- Since `A` is closed, `closure A = A`; rewrite to conclude.
  simpa [hA.closure_eq] using h