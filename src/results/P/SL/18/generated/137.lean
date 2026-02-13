

theorem closure_interior_eq_closure_of_open
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen (A : Set X)) :
    closure (interior (A : Set X)) = closure (A : Set X) := by
  simpa using
    (Topology.closure_eq_closure_interior_of_open (A := A) hA).symm