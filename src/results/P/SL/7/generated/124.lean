

theorem Topology.P1_union_open {X : Type*} [TopologicalSpace X] {A U : Set X} :
    Topology.P1 A → IsOpen U → Topology.P1 (A ∪ U) := by
  intro hP1A hUopen
  have hP1U : Topology.P1 U := Topology.IsOpen_P1 (A := U) hUopen
  exact Topology.P1_union (A := A) (B := U) hP1A hP1U