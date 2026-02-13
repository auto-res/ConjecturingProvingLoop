

theorem Topology.closureInterior_inter_frontier_eq_frontierInterior
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior A) ∩ frontier A = frontier (interior A) := by
  calc
    closure (interior A) ∩ frontier A
        = closure (interior A) \ interior A := by
          simpa using
            (Topology.closureInterior_inter_frontier_eq_closureInterior_diff_interior
                (A := A))
    _ = frontier (interior A) := by
          simpa using
            (Topology.frontier_interior_eq_closureInterior_diff_interior
                (A := A)).symm