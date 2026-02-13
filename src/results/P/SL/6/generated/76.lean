

theorem P3_implies_P2_of_closed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed (A : Set X)) :
    Topology.P3 (A : Set X) → Topology.P2 A := by
  intro hP3
  exact (Topology.P3_iff_P2_of_closed (A := A) hA).1 hP3