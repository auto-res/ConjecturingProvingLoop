

theorem Topology.isClosed_closure_inter
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    IsClosed (closure A ∩ closure B) := by
  have hA : IsClosed (closure A) := isClosed_closure
  have hB : IsClosed (closure B) := isClosed_closure
  exact hA.inter hB