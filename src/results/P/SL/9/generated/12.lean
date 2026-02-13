

theorem Topology.P2_iff_isOpen_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) : Topology.P2 (A := A) ↔ IsOpen A := by
  constructor
  · intro hP2
    have hP3 : Topology.P3 (A := A) := P2_implies_P3 hP2
    exact (Topology.P3_iff_isOpen_of_isClosed (A := A) hA_closed).1 hP3
  · intro hA_open
    exact Topology.P2_of_isOpen (A := A) hA_open