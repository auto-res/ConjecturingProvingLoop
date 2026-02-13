

theorem Topology.frontier_subset_compl_of_isOpen
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen (A : Set X)) :
    frontier (A : Set X) ⊆ Aᶜ := by
  simpa using
    ((Topology.isOpen_iff_frontier_subset_compl (A := A)).1 hA)