

theorem Topology.closed_P3_iff_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed A) :
    Topology.P3 (X := X) A ↔ IsOpen A := by
  constructor
  · intro hP3
    exact Topology.closed_P3_isOpen (X := X) (A := A) hClosed hP3
  · intro hOpen
    exact Topology.isOpen_implies_P3 (X := X) (A := A) hOpen