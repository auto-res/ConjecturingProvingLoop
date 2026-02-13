

theorem Topology.P3_univ {X : Type*} [TopologicalSpace X] :
    Topology.P3 (A := (Set.univ : Set X)) := by
  dsimp [Topology.P3]
  intro x _
  simp [closure_univ, interior_univ]