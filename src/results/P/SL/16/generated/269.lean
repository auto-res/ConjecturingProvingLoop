

theorem Topology.closure_interior_closure_union_eq_closure_interior_union_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (closure (A ∪ B))) =
      closure (interior (closure A ∪ closure B)) := by
  simpa [closure_union]