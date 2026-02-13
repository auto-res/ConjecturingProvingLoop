

theorem P2_univ {X : Type*} [TopologicalSpace X] :
    Topology.P2 (Set.univ : Set X) := by
  have h := (Topology.univ_has_all_P (X := X))
  exact h.2.1