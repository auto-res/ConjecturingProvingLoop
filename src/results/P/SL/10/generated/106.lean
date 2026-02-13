

theorem Topology.closure_union_interior_eq_union_closure_interior
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior A ∪ interior B) =
      closure (interior A) ∪ closure (interior B) := by
  simpa using closure_union (interior A) (interior B)