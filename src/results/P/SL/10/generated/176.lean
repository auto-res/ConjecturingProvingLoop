

theorem Topology.isOpen_of_P3_and_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP3 : Topology.P3 A) (hClosed : IsClosed A) : IsOpen A := by
  exact
    (Topology.P3_iff_isOpen_of_isClosed (X := X) (A := A) hClosed).1 hP3