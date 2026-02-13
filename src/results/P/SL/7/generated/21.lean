

theorem Topology.P1_of_P3_closed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) (hP3 : Topology.P3 A) : Topology.P1 A := by
  have hOpen : IsOpen A := (Topology.P3_closed_iff_isOpen (A := A) hA).1 hP3
  exact (Topology.IsOpen_P1_and_P3 (A := A) hOpen).1