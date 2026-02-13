

theorem Topology.closureInteriorClosure_empty_eq
    {X : Type*} [TopologicalSpace X] :
    closure (interior (closure (∅ : Set X))) = (∅ : Set X) := by
  simp