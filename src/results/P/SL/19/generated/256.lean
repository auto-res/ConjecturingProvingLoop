

theorem Topology.closure_union_right_closed {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hB : IsClosed B) :
    closure (A ∪ B) = closure A ∪ B := by
  simpa [closure_union, hB.closure_eq]