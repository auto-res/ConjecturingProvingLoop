

theorem P2_inter_univ {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A ∩ (Set.univ : Set X)) ↔ Topology.P2 A := by
  simpa [Set.inter_univ]