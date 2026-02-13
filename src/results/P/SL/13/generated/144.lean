

theorem Topology.all_P_univ {X : Type*} [TopologicalSpace X] :
    Topology.P1 (X := X) (Set.univ : Set X) ∧
      Topology.P2 (X := X) (Set.univ : Set X) ∧
        Topology.P3 (X := X) (Set.univ : Set X) := by
  exact
    ⟨Topology.P1_univ (X := X), Topology.P2_univ (X := X),
      Topology.P3_univ (X := X)⟩