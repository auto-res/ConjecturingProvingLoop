

theorem Topology.isClosed_closureInterior {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsClosed (closure (interior (A : Set X))) := by
  simpa using
    (isClosed_closure : IsClosed (closure (interior (A : Set X))))