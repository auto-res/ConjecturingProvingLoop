

theorem P2_of_open_closure_interior_eq_closure
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hEq : closure (interior (A : Set X)) = closure A)
    (hOpen : IsOpen (closure (interior A))) :
    Topology.P2 (A : Set X) := by
  -- From the equality of closures, deduce `P1` for `A`.
  have hP1 : Topology.P1 (A : Set X) :=
    ((Topology.P1_iff_closure_interior_eq_closure (A := A)).2 hEq)
  -- Combine `P1` with the openness assumption to obtain `P2`.
  exact
    Topology.P1_and_open_closure_interior_implies_P2
      (A := A) hP1 hOpen