

theorem P1_univ_iff_P2_univ {X : Type*} [TopologicalSpace X] :
    Topology.P1 (Set.univ : Set X) ↔ Topology.P2 (Set.univ : Set X) := by
  constructor
  · intro _; simpa using (Topology.P2_univ (X := X))
  · intro _; simpa using (Topology.P1_univ (X := X))