

theorem Topology.P3_empty {X : Type*} [TopologicalSpace X] :
    Topology.P3 (A := (∅ : Set X)) := by
  dsimp [Topology.P3]
  intro x hx
  cases hx