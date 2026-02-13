

theorem isOpen_of_closed_of_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed A) (hP3 : Topology.P3 A) : IsOpen A := by
  exact ((Topology.P3_iff_open_of_closed (A := A) hClosed).mp hP3)