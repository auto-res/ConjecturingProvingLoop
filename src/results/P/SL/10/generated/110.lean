

theorem Topology.isOpen_of_P2_and_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 A) (hClosed : IsClosed A) : IsOpen A := by
  have h_eq : interior A = A :=
    Topology.interior_eq_of_P2_and_isClosed (X := X) (A := A) hP2 hClosed
  have h_open_int : IsOpen (interior A) := isOpen_interior
  simpa [h_eq] using h_open_int