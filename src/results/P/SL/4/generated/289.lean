

theorem P1_P2_P3_univ {X : Type*} [TopologicalSpace X] :
    Topology.P1 (Set.univ : Set X) ∧
      Topology.P2 (Set.univ : Set X) ∧
        Topology.P3 (Set.univ : Set X) := by
  exact
    And.intro
      (Topology.P1_univ (X := X))
      (And.intro
        (Topology.P2_univ (X := X))
        (Topology.P3_univ (X := X)))