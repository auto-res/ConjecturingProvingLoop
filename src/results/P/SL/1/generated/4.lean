

theorem P1_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (interior A) := by
  dsimp [Topology.P1]
  simpa [interior_interior] using
    (subset_closure : interior A ⊆ closure (interior A))