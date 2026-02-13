

theorem Topology.isOpen_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P1 (X := X) A := by
  exact Topology.P2_implies_P1 (X := X) (A := A)
    (Topology.isOpen_implies_P2 (X := X) (A := A) hA)