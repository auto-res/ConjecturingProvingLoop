

theorem Topology.closure_union_eq_of_closed
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA_closed : IsClosed (A : Set X)) (hB_closed : IsClosed (B : Set X)) :
    closure (A ∪ B : Set X) = (A ∪ B : Set X) := by
  have hClosed : IsClosed (A ∪ B : Set X) := IsClosed.union hA_closed hB_closed
  simpa using hClosed.closure_eq