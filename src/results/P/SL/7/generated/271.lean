

theorem Topology.closure_union_of_closed {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsClosed A) (hB : IsClosed B) :
    closure (A ∪ B : Set X) = A ∪ B := by
  have hClosed : IsClosed (A ∪ B : Set X) := hA.union hB
  simpa using hClosed.closure_eq