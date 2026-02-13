

theorem Topology.closure_union_left_closed {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsClosed A) :
    closure (A ∪ B) = A ∪ closure B := by
  simpa [closure_union, hA.closure_eq]