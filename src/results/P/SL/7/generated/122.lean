

theorem Topology.P1_empty {X : Type*} [TopologicalSpace X] :
    Topology.P1 (∅ : Set X) := by
  exact (Topology.P1_P2_P3_empty (X := X)).1