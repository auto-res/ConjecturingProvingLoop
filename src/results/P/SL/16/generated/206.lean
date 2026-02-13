

theorem Topology.isClosed_of_closure_interior_eq {X : Type*} [TopologicalSpace X]
    {A : Set X} (h : closure (interior A) = A) : IsClosed A := by
  -- `closure (interior A)` is always closed.
  have hClosed : IsClosed (closure (interior A)) := isClosed_closure
  -- Rewrite using the provided equality.
  simpa [h] using hClosed