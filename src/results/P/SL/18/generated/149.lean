

theorem P2_union_P3 {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P2 A → Topology.P3 B → Topology.P3 (A ∪ B) := by
  intro hP2A hP3B
  have h : Topology.P3 (B ∪ A) :=
    Topology.P3_union_P2 (A := B) (B := A) hP3B hP2A
  simpa [Set.union_comm] using h