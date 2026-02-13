

theorem Topology.P2_empty {X : Type*} [TopologicalSpace X] :
    Topology.P2 (∅ : Set X) := by
  intro x hx
  cases hx