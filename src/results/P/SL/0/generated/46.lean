

theorem P2_implies_interior_closure_eq_interior_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A →
      interior (closure (A : Set X)) = interior (closure (interior A)) := by
  intro hP2
  have hP1 : Topology.P1 A :=
    (Topology.P2_implies_P1 (X := X) (A := A)) hP2
  exact
    (Topology.P1_implies_interior_closure_eq_interior_closure_interior
        (X := X) (A := A)) hP1