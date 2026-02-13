

theorem Topology.P2_iff_P3_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed A) : Topology.P2 A ↔ Topology.P3 A := by
  have hP2Open : Topology.P2 A ↔ IsOpen A :=
    Topology.P2_iff_isOpen_of_isClosed (X := X) (A := A) hClosed
  have hP3Open : Topology.P3 A ↔ IsOpen A :=
    Topology.P3_iff_isOpen_of_isClosed (X := X) (A := A) hClosed
  exact hP2Open.trans hP3Open.symm