

theorem Topology.closure_interior_closure_eq_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : Topology.P1 (A := A)) :
    closure (interior (closure A)) = closure (interior A) := by
  exact
    Topology.closure_interior_closure_eq_closure_interior_of_P1
      (X := X) (A := A) h