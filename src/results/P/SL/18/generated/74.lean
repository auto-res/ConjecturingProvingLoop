

theorem P3_union_P2 {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P3 A → Topology.P2 B → Topology.P3 (A ∪ B) := by
  intro hP3A hP2B
  have hP3B : Topology.P3 B := Topology.P2_implies_P3 hP2B
  exact Topology.P3_union hP3A hP3B