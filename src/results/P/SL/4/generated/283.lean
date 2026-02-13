

theorem closure_union_closed {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsClosed A) (hB : IsClosed B) :
    closure (A ∪ B) = A ∪ B := by
  -- The union of two closed sets is closed.
  have hClosed : IsClosed (A ∪ B) := hA.union hB
  -- Taking the closure of a closed set leaves it unchanged.
  simpa [hClosed.closure_eq]