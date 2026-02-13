

theorem P1_iff_closure_interior_eq_self_of_closed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed (A : Set X)) :
    Topology.P1 (A : Set X) ↔ closure (interior A) = A := by
  simpa [hA.closure_eq] using
    (Topology.P1_iff_closure_interior_eq_closure (A := A))