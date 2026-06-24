

theorem Topology.P1_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P1 A := by
  intro h
  exact Set.Subset.trans h interior_subset