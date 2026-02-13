

theorem Topology.frontier_subset_compl_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    frontier (A : Set X) ⊆ (interior A)ᶜ := by
  intro x hx
  exact hx.2