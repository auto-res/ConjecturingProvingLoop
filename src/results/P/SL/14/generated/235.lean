

theorem Topology.closureInteriorClosure_union_eq
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (closure (A ∪ B : Set X))) =
      closure (interior (closure A ∪ closure B)) := by
  simpa [closure_union]