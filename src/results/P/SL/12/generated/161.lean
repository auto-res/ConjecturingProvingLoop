

theorem Topology.isClosed_closure_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    IsClosed (closure (interior (A : Set X))) := by
  simpa using isClosed_closure