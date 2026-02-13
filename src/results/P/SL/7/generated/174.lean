

theorem Topology.P3_closureInteriorClosure_iff_isOpen
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure (interior (closure (A : Set X)))) ↔
      IsOpen (closure (interior (closure (A : Set X)))) := by
  have hClosed :
      IsClosed (closure (interior (closure (A : Set X)))) := isClosed_closure
  simpa using
    (Topology.P3_closed_iff_isOpen
        (A := closure (interior (closure (A : Set X)))) hClosed)