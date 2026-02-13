

theorem P3_univ_iff_P2_univ {X : Type*} [TopologicalSpace X] :
    Topology.P3 (Set.univ : Set X) ↔ Topology.P2 (Set.univ : Set X) := by
  constructor
  · intro _; exact Topology.P2_univ (X := X)
  · intro _; exact Topology.P3_univ (X := X)