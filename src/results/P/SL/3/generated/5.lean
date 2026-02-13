

theorem P3_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P3 (interior (A : Set X)) := by
  dsimp [Topology.P3]
  apply interior_maximal
  · exact subset_closure
  · exact isOpen_interior