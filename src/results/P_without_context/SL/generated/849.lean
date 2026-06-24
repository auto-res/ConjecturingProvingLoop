

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P1 A := by
  intro hP2
  dsimp [Topology.P1, Topology.P2] at *
  intro x hxA
  exact
    (interior_subset : interior (closure (interior A)) ⊆ closure (interior A))
      (hP2 hxA)