

theorem P1_closure_iff_closureInterior_eq_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P1 (closure A) ↔ closure (interior (closure A)) = closure A := by
  have h_closed : IsClosed (closure A) := isClosed_closure
  simpa using
    Topology.closed_P1_iff_closure_interior_eq (X := X) (A := closure A) h_closed