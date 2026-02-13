

theorem Topology.P3_closure_implies_P2_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (X:=X) (closure (A : Set X)) →
      Topology.P2 (X:=X) (closure (A : Set X)) := by
  intro hP3
  exact (Topology.P2_closure_iff_P3_closure (X:=X) (A:=A)).2 hP3