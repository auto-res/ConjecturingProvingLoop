

theorem Topology.frontier_compl_eq {X : Type*} [TopologicalSpace X] {A : Set X} :
    frontier (Aᶜ) = frontier A := by
  simpa [frontier_eq_closure_inter_closure_compl, Set.inter_comm, Set.compl_compl]