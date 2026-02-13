

theorem Topology.P2_closure_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure (A : Set X)) → Topology.P3 A := by
  intro hP2Cl
  have hP3Cl : Topology.P3 (closure (A : Set X)) :=
    (Topology.P2_closure_iff_P3_closure (A := A)).1 hP2Cl
  exact (Topology.P3_closure_implies_P3 (A := A)) hP3Cl