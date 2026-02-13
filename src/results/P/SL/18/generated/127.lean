

theorem closure_interior_eq_self_of_closed_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed (A : Set X)) (hP1 : Topology.P1 (A : Set X)) :
    closure (interior (A : Set X)) = A := by
  simpa using
    ((Topology.P1_closed_iff_closure_interior_eq (A := A) hClosed).1 hP1)