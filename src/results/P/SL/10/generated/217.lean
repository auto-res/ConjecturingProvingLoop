

theorem Topology.isClosed_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsClosed (closure (interior (closure A))) := by
  -- `closure (interior (closure A))` is a closure, hence closed.
  exact isClosed_closure