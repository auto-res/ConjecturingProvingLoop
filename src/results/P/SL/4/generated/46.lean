

theorem P2_iff_P3_of_closed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) :
    Topology.P2 A ↔ Topology.P3 A := by
  constructor
  · intro hP2
    exact Topology.P2_imp_P3 (A := A) hP2
  · intro hP3
    exact (Topology.P3_closed_imp_P2 (A := A) hA) hP3