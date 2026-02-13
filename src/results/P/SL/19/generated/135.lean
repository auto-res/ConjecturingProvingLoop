

theorem Topology.closure_closure_union_eq_closure_union {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (closure A ∪ B) = closure (A ∪ B) := by
  simp [closure_union, closure_closure]