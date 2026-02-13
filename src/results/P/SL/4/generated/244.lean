

theorem P3_union_open {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P3 A → IsOpen B → Topology.P3 (A ∪ B) := by
  intro hP3A hOpenB
  have hP3B : Topology.P3 B := Topology.isOpen_P3 (A := B) hOpenB
  exact Topology.P3_union (A := A) (B := B) hP3A hP3B