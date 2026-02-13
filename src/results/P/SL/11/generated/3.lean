

theorem P3_of_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P3 (interior A) := by
  dsimp [Topology.P3]
  simpa [interior_interior] using
    (interior_mono (subset_closure : interior A ⊆ closure (interior A)))