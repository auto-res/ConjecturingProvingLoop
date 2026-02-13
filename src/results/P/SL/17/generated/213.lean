

theorem Topology.frontier_eq_empty_of_clopen {X : Type*} [TopologicalSpace X]
    {A : Set X} (hClosed : IsClosed A) (hOpen : IsOpen A) :
    frontier A = (∅ : Set X) := by
  -- `frontier A = closure A \ interior A`; rewrite using the clopen hypotheses.
  simpa [frontier, hClosed.closure_eq, hOpen.interior_eq, Set.diff_self]