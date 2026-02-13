

theorem P2_iff_P3_empty {X : Type*} [TopologicalSpace X] :
    Topology.P2 (∅ : Set X) ↔ Topology.P3 (∅ : Set X) := by
  have hP2 : Topology.P2 (∅ : Set X) := Topology.P2_empty (X := X)
  have hP3 : Topology.P3 (∅ : Set X) := Topology.P3_empty (X := X)
  constructor
  · intro _; exact hP3
  · intro _; exact hP2