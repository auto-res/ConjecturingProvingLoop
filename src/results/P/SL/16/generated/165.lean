

theorem Topology.P1_univ {X : Type*} [TopologicalSpace X] :
    Topology.P1 (X := X) (Set.univ : Set X) := by
  dsimp [Topology.P1]
  intro x _
  simpa [closure_univ, interior_univ]