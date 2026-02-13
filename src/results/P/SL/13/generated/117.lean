

theorem Topology.P2_implies_closure_eq_closureInteriorClosure {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    Topology.P2 (X:=X) A → closure (A : Set X) = closure (interior (closure A)) := by
  intro hP2
  have hP3 : Topology.P3 (X:=X) A :=
    Topology.P2_implies_P3 (X:=X) (A:=A) hP2
  exact Topology.P3_implies_closure_eq_closureInteriorClosure (X:=X) (A:=A) hP3