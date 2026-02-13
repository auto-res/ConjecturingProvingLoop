

theorem Topology.frontier_empty {X : Type*} [TopologicalSpace X] :
    frontier (∅ : Set X) = (∅ : Set X) := by
  simp [frontier]