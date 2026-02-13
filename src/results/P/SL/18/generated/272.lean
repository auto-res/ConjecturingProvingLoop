

theorem interior_closure_eq_interior_closure_interior_of_open
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen (A : Set X)) :
    interior (closure (A : Set X)) =
      interior (closure (interior (A : Set X))) := by
  have hP2 : Topology.P2 (A : Set X) :=
    Topology.P2_of_open (A := A) hOpen
  exact
    Topology.interior_closure_eq_interior_closure_interior_of_P2
      (A := A) hP2