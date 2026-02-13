

theorem Topology.frontier_subset_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    frontier A ⊆ closure A := by
  intro x hx
  exact hx.1