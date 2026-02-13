

theorem Topology.P3_and_isClosed_implies_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP3 : Topology.P3 A) (hClosed : IsClosed A) : Topology.P2 A := by
  have hEquiv := (Topology.P2_iff_P3_of_isClosed (X := X) (A := A) hClosed)
  exact hEquiv.mpr hP3