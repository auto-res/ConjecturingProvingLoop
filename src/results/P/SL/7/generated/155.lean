

theorem Topology.P2_closureInteriorClosure_iff_isOpen {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P2 (closure (interior (closure (A : Set X)))) ↔
      IsOpen (closure (interior (closure (A : Set X)))) := by
  -- `closure (interior (closure A))` is closed, so we can use the closed‐set characterisation
  -- of `P2`.
  have hClosed : IsClosed (closure (interior (closure (A : Set X)))) := isClosed_closure
  simpa using
    (Topology.P2_closed_iff_isOpen
        (A := closure (interior (closure (A : Set X)))) hClosed)