

theorem Topology.interiorClosure_union_eq
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A ∪ B : Set X)) = interior (closure A ∪ closure B) := by
  simpa [closure_union]