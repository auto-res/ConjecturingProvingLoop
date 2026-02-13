

theorem Topology.P1_univ {X : Type*} [TopologicalSpace X] :
    Topology.P1 (A := (Set.univ : Set X)) := by
  dsimp [Topology.P1]
  intro x _
  simp [interior_univ, closure_univ]