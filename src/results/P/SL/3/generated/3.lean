

theorem P2_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P2 (interior (A : Set X)) := by
  dsimp [Topology.P2]
  have h : interior A ⊆ interior (closure (interior A)) := by
    apply interior_maximal
    · exact subset_closure
    · exact isOpen_interior
  simpa [interior_interior] using h