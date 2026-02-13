

theorem interior_satisfies_P2 {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P2 (interior A) := by
  dsimp [Topology.P2]
  simpa [interior_interior] using
    interior_maximal (subset_closure : interior A ⊆ closure (interior A))
      isOpen_interior