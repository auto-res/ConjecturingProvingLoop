

theorem P2_implies_P3_of_closed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed (A : Set X)) :
    Topology.P2 (A : Set X) → Topology.P3 A := by
  intro hP2
  exact (Topology.P3_iff_P2_of_closed (A := A) hA).2 hP2