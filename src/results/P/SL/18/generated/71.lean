

theorem closure_eq_closure_interior_closure_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 A) :
    closure A = closure (interior (closure A)) := by
  have hP3 : Topology.P3 A := Topology.P2_implies_P3 hP2
  exact Topology.closure_eq_closure_interior_closure_of_P3 hP3