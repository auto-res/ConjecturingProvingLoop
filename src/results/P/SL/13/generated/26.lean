

theorem Topology.P2_univ {X : Type*} [TopologicalSpace X] :
    Topology.P2 (X := X) (Set.univ : Set X) := by
  dsimp [Topology.P2]
  intro x hx
  simpa [interior_univ, closure_univ] using hx