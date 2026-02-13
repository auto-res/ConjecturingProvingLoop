

theorem closure_interior_eq_self_of_P1_closed
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed (A : Set X)) :
    Topology.P1 (A : Set X) → closure (interior A) = A := by
  intro hP1
  exact
    (Topology.P1_iff_closure_interior_eq_self_of_closed
        (A := A) hA).1 hP1