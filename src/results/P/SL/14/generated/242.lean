

theorem Topology.P2_empty {X : Type*} [TopologicalSpace X] :
    Topology.P2 (∅ : Set X) := by
  -- We reuse the existing result that the empty set satisfies all three properties.
  have h := Topology.empty_satisfies_P1_P2_P3 (X := X)
  exact h.2.1