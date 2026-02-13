

theorem P1_empty_iff_P2_empty {X : Type*} [TopologicalSpace X] :
    Topology.P1 (∅ : Set X) ↔ Topology.P2 (∅ : Set X) := by
  constructor
  · intro _
    exact Topology.P2_empty (X := X)
  · intro _
    exact Topology.P1_empty (X := X)