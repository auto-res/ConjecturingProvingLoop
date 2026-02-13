

theorem Topology.isClosed_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsClosed (closure (interior A)) := by
  simpa using isClosed_closure (s := interior A)