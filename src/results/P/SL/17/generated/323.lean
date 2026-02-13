

theorem Topology.frontier_compl_eq_frontier {X : Type*} [TopologicalSpace X] {A : Set X} :
    frontier (Aᶜ) = frontier A := by
  simpa using frontier_compl (A := A)