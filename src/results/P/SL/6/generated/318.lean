

theorem closure_inter_of_closures
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (closure (A : Set X) ∩ closure B) = closure A ∩ closure B := by
  -- The intersection of two closed sets is closed.
  have hClosed : IsClosed (closure (A : Set X) ∩ closure B) := by
    exact
      (isClosed_closure (s := (A : Set X))).inter
        (isClosed_closure (s := (B : Set X)))
  -- Taking the closure of a closed set leaves it unchanged.
  simpa [hClosed.closure_eq]