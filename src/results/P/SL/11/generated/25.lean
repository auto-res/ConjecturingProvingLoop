

theorem P2_univ {X : Type*} [TopologicalSpace X] :
    Topology.P2 (Set.univ : Set X) := by
  dsimp [Topology.P2]
  simp [interior_univ, closure_univ]