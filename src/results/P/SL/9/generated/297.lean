

theorem Topology.frontier_compl_swap {X : Type*} [TopologicalSpace X] (A : Set X) :
    frontier (A : Set X) = frontier (Aᶜ) := by
  simpa using (frontier_compl (A := A)).symm