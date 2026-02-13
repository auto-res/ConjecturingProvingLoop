

theorem Topology.frontier_eq_closure_interior_diff_interior_of_P2 {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A := A) →
      frontier A = closure (interior A) \ interior A := by
  intro hP2
  calc
    frontier A
        = frontier (interior A) := by
          simpa using
            (Topology.frontier_eq_frontier_interior_of_P2 (A := A) hP2)
    _ = closure (interior A) \ interior A := by
          simpa using
            (Topology.frontier_interior_eq_closure_interior_diff_interior
              (X := X) (A := A))