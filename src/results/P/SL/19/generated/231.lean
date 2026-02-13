

theorem Topology.isClosed_closure_inter_closure {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    IsClosed (closure A ∩ closure B) := by
  exact (isClosed_closure (s := A)).inter (isClosed_closure (s := B))