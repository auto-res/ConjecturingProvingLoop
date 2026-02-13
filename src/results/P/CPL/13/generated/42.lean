

theorem P2_univ_iff {X : Type*} [TopologicalSpace X] : (Topology.P2 (Set.univ : Set X)) ↔ True := by
  constructor
  · intro _; trivial
  · intro _; exact Topology.P2_univ (X := X)