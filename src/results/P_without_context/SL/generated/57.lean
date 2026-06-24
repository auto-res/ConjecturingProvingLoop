

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P1 A := by
  intro hA
  dsimp [Topology.P2, Topology.P1] at *
  have hInt : interior (closure (interior A)) ⊆ closure (interior A) := by
    simpa using interior_subset (s := closure (interior A))
  exact hA.trans hInt