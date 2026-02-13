

theorem Topology.closure_union_eq_of_isClosed {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hA : IsClosed A) (hB : IsClosed B) :
    closure (A ∪ B) = A ∪ B := by
  have hClosed : IsClosed (A ∪ B) := hA.union hB
  simpa using hClosed.closure_eq