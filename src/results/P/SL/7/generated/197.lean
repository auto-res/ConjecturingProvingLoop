

theorem Topology.isOpen_of_P2_closed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) (hP2 : Topology.P2 A) : IsOpen A := by
  exact (Topology.P2_closed_iff_isOpen (A := A) hA).1 hP2