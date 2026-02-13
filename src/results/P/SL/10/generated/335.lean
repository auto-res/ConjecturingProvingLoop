

theorem Topology.boundary_univ {X : Type*} [TopologicalSpace X] :
    closure (Set.univ : Set X) \ interior (Set.univ : Set X) = (∅ : Set X) := by
  simp