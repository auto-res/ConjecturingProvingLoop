

theorem closure_inter_eq_self_of_closed
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA_closed : IsClosed (A : Set X)) (hB_closed : IsClosed (B : Set X)) :
    closure (A ∩ B : Set X) = A ∩ B := by
  -- The intersection of two closed sets is itself closed.
  have hClosed : IsClosed (A ∩ B : Set X) := hA_closed.inter hB_closed
  -- The closure of a closed set equals the set itself.
  simpa using hClosed.closure_eq