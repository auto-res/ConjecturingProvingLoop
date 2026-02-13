

theorem P3_univ {X : Type*} [TopologicalSpace X] :
    Topology.P3 (Set.univ : Set X) := by
  simpa using (Topology.P123_univ (X := X)).2.2