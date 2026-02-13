

theorem Topology.P2_implies_closure_eq_closureInterior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P2 (X:=X) A → closure (A : Set X) = closure (interior A) := by
  intro hP2
  have hP1 : Topology.P1 (X:=X) A :=
    Topology.P2_implies_P1 (X:=X) (A:=A) hP2
  exact (Topology.P1_iff_closure_eq_closureInterior (X:=X) (A:=A)).1 hP1