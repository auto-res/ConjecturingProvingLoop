

theorem P3_closure_interior_iff_open_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure (interior (A : Set X))) ↔
      IsOpen (closure (interior (A : Set X))) := by
  have hClosed : IsClosed (closure (interior (A : Set X))) := isClosed_closure
  simpa using
    (Topology.P3_closed_iff_open
      (A := closure (interior (A : Set X))) hClosed)