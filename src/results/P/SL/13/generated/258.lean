

theorem Topology.closure_inter_closures_eq_inter_closures {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (closure (A : Set X) ∩ closure B) = closure A ∩ closure B := by
  -- The intersection of two closed sets is closed.
  have h_closed : IsClosed (closure (A : Set X) ∩ closure B) :=
    (isClosed_closure : IsClosed (closure (A : Set X))).inter
      (isClosed_closure : IsClosed (closure B))
  -- Taking the closure of a closed set yields the set itself.
  simpa using h_closed.closure_eq