

theorem Topology.closure_interior_union_eq_closure_union_interiors
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (A : Set X)) ∪ closure (interior B) =
      closure (interior A ∪ interior B) := by
  simpa using
    (closure_union (interior (A : Set X)) (interior (B : Set X))).symm