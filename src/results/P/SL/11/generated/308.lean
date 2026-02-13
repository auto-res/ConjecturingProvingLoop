

theorem P2_closure_interior_closure_iff_open {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P2 (closure (interior (closure A))) ↔
      IsOpen (closure (interior (closure A))) := by
  have hClosed : IsClosed (closure (interior (closure A))) := isClosed_closure
  simpa using
    (Topology.P2_iff_open_of_closed
        (A := closure (interior (closure A))) hClosed)