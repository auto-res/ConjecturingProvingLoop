

theorem Topology.subset_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    A ⊆ closure A := by
  exact Set.subset_closure