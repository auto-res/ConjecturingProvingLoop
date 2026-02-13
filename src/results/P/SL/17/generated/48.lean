

theorem Topology.P2_univ {X : Type*} [TopologicalSpace X] :
    Topology.P2 (Set.univ : Set X) := by
  simpa using (Topology.P_properties_univ (X := X)).right.left