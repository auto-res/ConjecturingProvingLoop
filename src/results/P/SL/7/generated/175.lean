

theorem Topology.P2_univ {X : Type*} [TopologicalSpace X] :
    Topology.P2 (Set.univ : Set X) := by
  exact (Topology.P1_P2_P3_univ (X := X)).2.1