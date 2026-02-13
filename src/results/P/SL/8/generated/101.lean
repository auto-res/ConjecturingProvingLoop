

theorem P2_closureInteriorClosure_iff_isOpen_closureInteriorClosure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure (interior (closure A))) ↔
      IsOpen (closure (interior (closure A))) := by
  have h_closed : IsClosed (closure (interior (closure A))) := isClosed_closure
  simpa using
    Topology.closed_P2_iff_isOpen (X := X)
      (A := closure (interior (closure A))) h_closed