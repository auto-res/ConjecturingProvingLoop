

theorem Topology.P2_implies_P1_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 (A := A)) : Topology.P1 (A := closure A) := by
  have hP3 : Topology.P3 (A := A) := P2_implies_P3 hP2
  exact Topology.P3_implies_P1_closure (A := A) hP3