

theorem Topology.closure_frontier_subset_of_isClosed {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    IsClosed A → closure (frontier (A : Set X)) ⊆ A := by
  intro hClosed
  -- We already have `closure (frontier A) ⊆ closure A`.
  have h : closure (frontier (A : Set X)) ⊆ closure (A : Set X) :=
    Topology.closure_frontier_subset_closure (A := A)
  -- Since `A` is closed, `closure A = A`; rewrite and conclude.
  simpa [hClosed.closure_eq] using h