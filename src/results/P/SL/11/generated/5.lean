

theorem P2_of_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P2 (interior A) := by
  dsimp [Topology.P2]
  simpa [interior_interior] using
    (interior_mono (subset_closure : interior A ⊆ closure (interior A)))