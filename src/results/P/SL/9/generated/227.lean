

theorem Topology.frontier_univ {X : Type*} [TopologicalSpace X] :
    frontier (Set.univ : Set X) = (∅ : Set X) := by
  classical
  simp [frontier, closure_univ, interior_univ]