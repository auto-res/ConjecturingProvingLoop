

theorem Topology.P2_iff_P3_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) :
    Topology.P2 (A := A) ↔ Topology.P3 (A := A) := by
  constructor
  · intro hP2
    exact (Topology.P2_implies_P3 (A := A)) hP2
  · intro hP3
    exact (Topology.P3_implies_P2_of_isClosed (A := A) hA) hP3