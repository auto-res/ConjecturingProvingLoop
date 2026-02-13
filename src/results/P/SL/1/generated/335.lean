

theorem Topology.P2_union_interior_self {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P2 (A ∪ interior A) := by
  intro hP2A
  have hP2Int : Topology.P2 (interior A) := P2_interior (A := A)
  simpa using
    (Topology.P2_union (A := A) (B := interior A) hP2A hP2Int)