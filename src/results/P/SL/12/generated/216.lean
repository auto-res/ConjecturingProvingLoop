

theorem Topology.isClosed_closure_inter_closure {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    IsClosed ((closure (A : Set X)) ∩ closure B) := by
  have hA : IsClosed (closure (A : Set X)) := isClosed_closure
  have hB : IsClosed (closure (B : Set X)) := isClosed_closure
  exact hA.inter hB