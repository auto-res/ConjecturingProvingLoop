

theorem P3_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen (A : Set X)) :
    Topology.P3 A := by
  dsimp [Topology.P3]
  apply interior_maximal
  · exact subset_closure
  · exact hA