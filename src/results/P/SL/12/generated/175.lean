

theorem Topology.P2_closure_interior_iff_P3_closure_interior
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P2 (X := X) (closure (interior A)) ↔
      Topology.P3 (X := X) (closure (interior A)) := by
  have h_closed : IsClosed (closure (interior (A : Set X))) := isClosed_closure
  simpa using
    (Topology.P2_iff_P3_of_isClosed
      (X := X) (A := closure (interior A)) h_closed)