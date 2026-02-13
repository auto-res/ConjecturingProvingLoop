

theorem Topology.interior_closure_empty {X : Type*} [TopologicalSpace X] :
    interior (closure (∅ : Set X)) = (∅ : Set X) := by
  simpa [closure_empty, interior_empty]