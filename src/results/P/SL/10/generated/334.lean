

theorem Topology.boundary_empty {X : Type*} [TopologicalSpace X] :
    closure (∅ : Set X) \ interior (∅ : Set X) = (∅ : Set X) := by
  simp