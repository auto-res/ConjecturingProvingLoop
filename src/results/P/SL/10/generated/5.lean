

theorem Topology.isOpen_implies_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P2 A := by
  dsimp [Topology.P2]
  simpa [hA.interior_eq] using (interior_maximal subset_closure hA)