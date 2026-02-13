

theorem Topology.frontier_closure_eq_closure_diff_interiorClosure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    frontier (closure (A : Set X)) =
      closure A \ interior (closure A) := by
  simpa using
    (Topology.frontier_eq_closure_diff_interior
      (A := closure A))