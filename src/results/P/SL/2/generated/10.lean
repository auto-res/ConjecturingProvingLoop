

theorem Topology.P2_implies_closure_interior_eq_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P2 A → closure (interior A) = closure A := by
  intro hP2
  have hP1 : Topology.P1 A := Topology.P2_implies_P1 (A := A) hP2
  exact Topology.P1_implies_closure_interior_eq_closure (A := A) hP1