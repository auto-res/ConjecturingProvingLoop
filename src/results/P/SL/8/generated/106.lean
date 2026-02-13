

theorem P3_closureInteriorClosure_iff_isOpen_closureInteriorClosure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure (interior (closure A))) ↔
      IsOpen (closure (interior (closure A))) := by
  have h_closed : IsClosed (closure (interior (closure A))) := isClosed_closure
  simpa using
    Topology.closed_P3_iff_isOpen (X := X)
      (A := closure (interior (closure A))) h_closed