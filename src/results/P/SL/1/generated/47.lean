

theorem Topology.isOpen_of_P2_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) (hP2 : Topology.P2 A) :
    IsOpen A := by
  exact (Topology.P2_iff_isOpen_of_isClosed (A := A) hA).1 hP2