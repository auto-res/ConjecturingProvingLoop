

theorem closure_inter_closure_eq {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (closure A ∩ closure B) = closure A ∩ closure B := by
  -- The intersection of two closed sets is closed.
  have hClosed : IsClosed (closure A ∩ closure B) :=
    (isClosed_closure : IsClosed (closure A)).inter
      (isClosed_closure : IsClosed (closure B))
  -- Taking the closure of a closed set leaves it unchanged.
  simpa using hClosed.closure_eq