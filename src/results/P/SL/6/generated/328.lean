

theorem closure_inter_eq_inter_of_closed
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsClosed (A : Set X)) (hB : IsClosed (B : Set X)) :
    closure ((A ∩ B) : Set X) = A ∩ B := by
  -- The intersection of two closed sets is closed.
  have hClosed : IsClosed ((A ∩ B) : Set X) := hA.inter hB
  -- Taking the closure of a closed set leaves it unchanged.
  simpa using hClosed.closure_eq