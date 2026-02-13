

theorem Topology.closureInteriorClosure_isClosed {X : Type*} [TopologicalSpace X]
    (A : Set X) : IsClosed (closure (interior (closure A))) := by
  simpa using
    (isClosed_closure : IsClosed (closure (interior (closure A))))