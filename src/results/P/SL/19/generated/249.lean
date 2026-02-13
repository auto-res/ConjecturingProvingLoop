

theorem Topology.closure_frontier_eq_closure_diff_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    closure (frontier A) = closure A \ interior A := by
  have h := Topology.closure_frontier_eq_frontier (A := A)
  simpa [h] using
    (Topology.closure_diff_interior_eq_frontier (A := A)).symm