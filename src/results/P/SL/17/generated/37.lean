

theorem Topology.P3_univ {X : Type*} [TopologicalSpace X] :
    Topology.P3 (Set.univ : Set X) := by
  have h := Topology.P_properties_univ (X := X)
  exact h.right.right