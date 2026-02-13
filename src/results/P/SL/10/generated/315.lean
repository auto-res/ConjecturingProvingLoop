

theorem Topology.closure_closure_inter_closed_eq {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hB : IsClosed B) :
    closure (closure A ∩ B) = closure A ∩ B := by
  have hClosed : IsClosed (closure A ∩ B) :=
    (isClosed_closure : IsClosed (closure A)).inter hB
  simpa using hClosed.closure_eq