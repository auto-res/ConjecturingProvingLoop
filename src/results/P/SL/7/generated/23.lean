

theorem Topology.P2_iff_P3_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) : Topology.P2 A ↔ Topology.P3 A := by
  constructor
  · intro hP2
    exact Topology.P2_implies_P3 hP2
  · intro hP3
    have hOpen : IsOpen A := (Topology.P3_closed_iff_isOpen (A := A) hA).1 hP3
    exact (IsOpen_P2 (A := A) hOpen)