

theorem Topology.P1_empty {X : Type*} [TopologicalSpace X] :
    Topology.P1 (∅ : Set X) := by
  unfold Topology.P1
  intro x hx
  cases hx