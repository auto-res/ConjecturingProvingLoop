

theorem Topology.P1_P2_P3_empty {X : Type*} [TopologicalSpace X] :
    Topology.P1 (X := X) (∅ : Set X) ∧
      Topology.P2 (X := X) (∅ : Set X) ∧
      Topology.P3 (X := X) (∅ : Set X) := by
  have h1 : Topology.P1 (X := X) (∅ : Set X) := by
    dsimp [Topology.P1]
    simp
  have h2 : Topology.P2 (X := X) (∅ : Set X) := by
    dsimp [Topology.P2]
    simp
  have h3 : Topology.P3 (X := X) (∅ : Set X) := by
    dsimp [Topology.P3]
    simp
  exact And.intro h1 (And.intro h2 h3)