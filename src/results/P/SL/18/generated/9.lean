

theorem interior_closure_eq_interior_closure_interior_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 A) :
    interior (closure A) = interior (closure (interior A)) := by
  have hP1 : Topology.P1 A := Topology.P2_implies_P1 hP2
  exact Topology.interior_closure_eq_interior_closure_interior_of_P1 hP1