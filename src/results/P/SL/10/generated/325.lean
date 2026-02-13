

theorem Topology.closure_interior_union_eq_closure_union {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (interior A ∪ B) = closure (interior A) ∪ closure B := by
  simpa using closure_union (interior A) B