

theorem Topology.isOpen_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P3 A := by
  dsimp [Topology.P3]
  exact interior_maximal subset_closure hA