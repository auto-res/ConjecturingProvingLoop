

theorem Topology.P1_univ {X : Type*} [TopologicalSpace X] :
    Topology.P1 (Set.univ : Set X) := by
  simpa using (Topology.P1_P2_P3_univ (X := X)).1