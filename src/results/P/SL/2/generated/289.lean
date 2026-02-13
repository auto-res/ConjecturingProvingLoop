

theorem Topology.frontier_def_eq_closure_diff_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    frontier (A : Set X) = closure (A : Set X) \ interior (A : Set X) := by
  rfl