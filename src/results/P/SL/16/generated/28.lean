

theorem Topology.closed_P2_iff_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed A) :
    Topology.P2 (X := X) A ↔ IsOpen A := by
  constructor
  · intro hP2
    exact Topology.closed_P2_isOpen (X := X) (A := A) hClosed hP2
  · intro hOpen
    exact Topology.isOpen_implies_P2 (X := X) (A := A) hOpen