

theorem Topology.P2_implies_P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (X:=X) A → Topology.P1 (X:=X) (closure (A : Set X)) := by
  intro hP2
  have hP3 : Topology.P3 (X:=X) A :=
    Topology.P2_implies_P3 (X:=X) (A:=A) hP2
  exact Topology.P3_implies_P1_closure (X:=X) (A:=A) hP3