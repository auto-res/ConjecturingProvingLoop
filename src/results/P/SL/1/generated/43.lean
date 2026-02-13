

theorem Topology.P1_closure_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P1 (closure A) := by
  intro hP2
  have hP3 : Topology.P3 A := P2_implies_P3 (A := A) hP2
  exact Topology.P1_closure_of_P3 (A := A) hP3