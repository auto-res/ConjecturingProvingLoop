

theorem Topology.closure_union_closure_right_eq_closure_union
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A ∪ closure B) = closure (A ∪ B) := by
  simpa [closure_union, closure_closure]