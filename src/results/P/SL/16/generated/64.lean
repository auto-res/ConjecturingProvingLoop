

theorem Topology.interior_closure_interior_eq_interior_closure_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 (X := X) A) :
    interior (closure (interior A)) = interior (closure A) := by
  have hP1 : Topology.P1 (X := X) A :=
    Topology.P2_implies_P1 (X := X) (A := A) hP2
  exact
    Topology.interior_closure_interior_eq_interior_closure_of_P1
      (X := X) (A := A) hP1