

theorem P2_union_empty {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A ∪ (∅ : Set X)) ↔ Topology.P2 A := by
  simpa [Set.union_empty]