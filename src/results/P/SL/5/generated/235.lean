

theorem closure_interior_eq_closure_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : Topology.P2 (X := X) A) :
    closure (interior A) = closure (A : Set X) := by
  simpa using
    (Topology.closure_eq_closure_interior_of_P2 (X := X) (A := A) hA).symm