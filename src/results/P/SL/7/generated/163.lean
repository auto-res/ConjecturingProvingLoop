

theorem Topology.P2_empty {X : Type*} [TopologicalSpace X] :
    Topology.P2 (∅ : Set X) := by
  exact (Topology.P1_P2_P3_empty (X := X)).2.1

theorem Topology.P3_empty {X : Type*} [TopologicalSpace X] :
    Topology.P3 (∅ : Set X) := by
  exact (Topology.P1_P2_P3_empty (X := X)).2.2