

theorem Topology.isClosed_closure_interior_union
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    IsClosed (closure (interior A) ∪ closure (interior B)) := by
  have hA : IsClosed (closure (interior A)) := isClosed_closure
  have hB : IsClosed (closure (interior B)) := isClosed_closure
  exact hA.union hB