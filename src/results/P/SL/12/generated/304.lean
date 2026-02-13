

theorem Topology.isClosed_closure_inter_closure_interior
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    IsClosed (closure (A : Set X) ∩ closure (interior B)) := by
  -- Both factors of the intersection are closed.
  have hA : IsClosed (closure (A : Set X)) := isClosed_closure
  have hB : IsClosed (closure (interior (B : Set X))) := isClosed_closure
  -- The intersection of two closed sets is closed.
  exact hA.inter hB