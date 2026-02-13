

theorem interior_satisfies_P2 {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P2 (interior A) := by
  dsimp [Topology.P2]
  have h : interior A ⊆ interior (closure (interior A)) :=
    interior_maximal subset_closure isOpen_interior
  simpa [interior_interior] using h