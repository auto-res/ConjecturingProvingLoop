

theorem Topology.boundary_eq_closure_diff_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    closure A \ interior A = closure A ∩ (interior A)ᶜ := by
  ext x
  simp [Set.diff_eq, Set.inter_comm]