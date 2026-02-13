

theorem Topology.closure_frontier_eq_closure_diff_interior
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (frontier (A : Set X)) = closure A \ interior A := by
  calc
    closure (frontier (A : Set X))
        = frontier (A : Set X) := by
          simpa using (Topology.closureFrontier_eq_self (A := A))
    _ = closure A \ interior A := by
          simpa using
            (Topology.frontier_eq_closure_diff_interior (A := A))