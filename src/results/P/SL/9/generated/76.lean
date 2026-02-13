

theorem Topology.closureInterior_closure_eq_closure_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 (A := A)) :
    closure (interior (closure A)) = closure A := by
  have hP3 : Topology.P3 (A := A) := P2_implies_P3 hP2
  exact Topology.closureInterior_closure_eq_closure_of_P3 (A := A) hP3