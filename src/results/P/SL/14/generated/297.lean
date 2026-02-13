

theorem Topology.interiorClosure_empty_eq {X : Type*} [TopologicalSpace X] :
    interior (closure (∅ : Set X)) = (∅ : Set X) := by
  simp [closure_empty, interior_empty]