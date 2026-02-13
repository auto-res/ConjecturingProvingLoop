

theorem P1_union_P2 {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P1 A → Topology.P2 B → Topology.P1 (A ∪ B) := by
  intro hP1A hP2B
  have hP1B : Topology.P1 B := Topology.P2_implies_P1 hP2B
  exact Topology.P1_union hP1A hP1B