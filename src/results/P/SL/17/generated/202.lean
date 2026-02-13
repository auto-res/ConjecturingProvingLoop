

theorem Topology.isClosed_of_closure_interior_eq_self {X : Type*} [TopologicalSpace X]
    {A : Set X} (h : closure (interior A) = A) : IsClosed A := by
  -- `closure (interior A)` is always a closed set.
  have hClosed : IsClosed (closure (interior A)) := isClosed_closure
  -- Rewriting with the given equality yields the desired result.
  simpa [h] using hClosed