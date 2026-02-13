

theorem Topology.P2_iff_isOpen_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) :
    Topology.P2 A ↔ IsOpen A := by
  constructor
  · intro hP2
    have hP3 : Topology.P3 A := P2_implies_P3 (A := A) hP2
    exact (Topology.P3_iff_isOpen_of_isClosed (A := A) hA).1 hP3
  · intro hOpen
    exact Topology.P2_of_isOpen (A := A) hOpen