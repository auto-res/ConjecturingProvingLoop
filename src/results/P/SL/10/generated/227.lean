

theorem Topology.compl_boundary_eq_union_interior_compl_closure {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    (closure A \ interior A)ᶜ = interior A ∪ (closure A)ᶜ := by
  classical
  ext x
  simp [Set.diff_eq, Set.compl_inter, Set.compl_compl, Set.union_comm]