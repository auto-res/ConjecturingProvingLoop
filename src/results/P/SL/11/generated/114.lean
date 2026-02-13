

theorem isOpen_of_closed_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed A) (hP2 : Topology.P2 A) : IsOpen A := by
  exact ((Topology.P2_iff_open_of_closed (A := A) hClosed).1 hP2)