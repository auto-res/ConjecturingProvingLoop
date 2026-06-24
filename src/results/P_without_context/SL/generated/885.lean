

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A := A) → Topology.P1 (A := A) := by
  intro hP2
  dsimp [Topology.P1, Topology.P2] at hP2
  exact Set.Subset.trans hP2 (by
    simpa using
      (interior_subset : interior (closure (interior A)) ⊆ closure (interior A)))