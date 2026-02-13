

theorem Topology.P3_union_open {X : Type*} [TopologicalSpace X] {A U : Set X} :
    Topology.P3 A → IsOpen U → Topology.P3 (A ∪ U) := by
  intro hP3A hU_open
  have hP3U : Topology.P3 U := (Topology.IsOpen_P1_and_P3 (A := U) hU_open).2
  exact Topology.P3_union hP3A hP3U