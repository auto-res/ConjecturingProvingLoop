

theorem P2_closure_interior_iff_open_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure (interior (A : Set X))) ↔ IsOpen (closure (interior A)) := by
  have hClosed : IsClosed (closure (interior (A : Set X))) := isClosed_closure
  simpa using
    (Topology.P2_iff_open_of_closed
      (A := closure (interior (A : Set X))) hClosed)