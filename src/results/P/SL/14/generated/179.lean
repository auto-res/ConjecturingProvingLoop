

theorem Topology.P3_univ {X : Type*} [TopologicalSpace X] :
    Topology.P3 (Set.univ : Set X) := by
  exact (Topology.univ_satisfies_P1_P2_P3 (X := X)).2.2