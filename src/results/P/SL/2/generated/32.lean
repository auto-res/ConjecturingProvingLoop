

theorem Topology.P2_implies_closure_interior_closure_eq_closure {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → closure (interior (closure A)) = closure A := by
  intro hP2
  have hP3 : Topology.P3 A := Topology.P2_implies_P3 (A := A) hP2
  exact Topology.P3_implies_closure_interior_closure_eq_closure (A := A) hP3