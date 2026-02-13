

theorem Topology.P3_empty {X : Type*} [TopologicalSpace X] :
    Topology.P3 (∅ : Set X) := by
  simpa using
    (Topology.empty_satisfies_P1_P2_P3 (X := X)).2.2