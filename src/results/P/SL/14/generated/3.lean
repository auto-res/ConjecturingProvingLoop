

theorem Topology.isOpen_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P3 A := by
  exact Topology.P2_implies_P3 (Topology.isOpen_implies_P2 hA)