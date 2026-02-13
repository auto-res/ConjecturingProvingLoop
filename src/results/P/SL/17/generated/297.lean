

theorem Topology.frontier_univ {X : Type*} [TopologicalSpace X] :
    frontier (Set.univ : Set X) = (∅ : Set X) := by
  simp [frontier]