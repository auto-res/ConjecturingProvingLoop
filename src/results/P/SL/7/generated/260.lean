

theorem Topology.interiorClosureInterior_empty {X : Type*} [TopologicalSpace X] :
    interior (closure (interior (∅ : Set X))) = (∅ : Set X) := by
  simp