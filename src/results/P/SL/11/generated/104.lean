

theorem closure_interior_eq_closure_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : Topology.P2 A) : closure (interior A) = closure A := by
  simpa using (Topology.closure_eq_closure_interior_of_P2 (A := A) h).symm