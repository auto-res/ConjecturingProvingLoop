

theorem Topology.P2_union_open {X : Type*} [TopologicalSpace X] {A U : Set X} :
    Topology.P2 A → IsOpen U → Topology.P2 (A ∪ U) := by
  intro hP2A hUopen
  have hP2U : Topology.P2 U := IsOpen_P2 (A := U) hUopen
  exact Topology.P2_union (A := A) (B := U) hP2A hP2U