

theorem Topology.P3_univ {X : Type*} [TopologicalSpace X] :
    Topology.P3 (Set.univ : Set X) := by
  simpa using (Topology.P1_P2_P3_univ (X := X)).2.2