

theorem Topology.frontier_subset_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    frontier (A : Set X) ⊆ closure (A : Set X) := by
  intro x hx
  exact hx.1