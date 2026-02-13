

theorem Topology.closure_inter_closure_eq {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (closure A ∩ closure B) = closure A ∩ closure B := by
  have h_closed : IsClosed (closure A ∩ closure B) :=
    (isClosed_closure : IsClosed (closure A)).inter
      (isClosed_closure : IsClosed (closure B))
  simpa using h_closed.closure_eq