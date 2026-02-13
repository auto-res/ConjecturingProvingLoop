

theorem Topology.closure_inter_closure_eq_inter_closure {X : Type*}
    [TopologicalSpace X] {A B : Set X} :
    closure (closure A ∩ closure B) = closure A ∩ closure B := by
  have hClosed : IsClosed (closure A ∩ closure B) :=
    (isClosed_closure (s := A)).inter (isClosed_closure (s := B))
  simpa using hClosed.closure_eq