

theorem Topology.isOpen_of_P3_closed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) (hP3 : Topology.P3 A) : IsOpen A := by
  exact (Topology.P3_closed_iff_isOpen (A := A) hA).1 hP3