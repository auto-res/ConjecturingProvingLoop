

theorem isOpen_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P3 A := by
  exact (P2_implies_P3 (X := X) (A := A)) (isOpen_implies_P2 (X := X) (A := A) hA)