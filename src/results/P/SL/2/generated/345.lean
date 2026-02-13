

theorem Topology.closure_frontier_eq_closure_diff_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    closure (frontier (A : Set X)) =
      closure (A : Set X) \ interior (A : Set X) := by
  -- The frontier of any set is closed, hence equal to its own closure.
  have hClosed : IsClosed (frontier (A : Set X)) := isClosed_frontier
  calc
    closure (frontier (A : Set X))
        = frontier (A : Set X) := by
          simpa using hClosed.closure_eq
    _ = closure (A : Set X) \ interior (A : Set X) := rfl