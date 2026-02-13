

theorem Topology.closure_closure_diff_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    closure (closure A \ interior A) = closure A \ interior A := by
  -- The set `closure A \ interior A` is closed, hence equal to its closure.
  have hClosed : IsClosed (closure A \ interior A) :=
    Topology.isClosed_closure_diff_interior (X := X) (A := A)
  simpa using hClosed.closure_eq