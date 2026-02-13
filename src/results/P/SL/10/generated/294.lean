

theorem Topology.isClosed_closure_inter_closure {X : Type*} [TopologicalSpace X]
    {A B : Set X} : IsClosed (closure A ∩ closure B) := by
  simpa using
    (isClosed_closure : IsClosed (closure A)).inter
      (isClosed_closure : IsClosed (closure B))