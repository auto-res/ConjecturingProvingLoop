

theorem Topology.P3_empty {X : Type*} [TopologicalSpace X] :
    Topology.P3 (∅ : Set X) := by
  intro x hx
  cases hx