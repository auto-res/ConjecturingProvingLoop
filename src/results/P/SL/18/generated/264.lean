

theorem closure_union_eq_self_of_closed
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA_closed : IsClosed (A : Set X)) (hB_closed : IsClosed (B : Set X)) :
    closure (A ∪ B : Set X) = A ∪ B := by
  have hClosed : IsClosed (A ∪ B : Set X) := hA_closed.union hB_closed
  exact hClosed.closure_eq