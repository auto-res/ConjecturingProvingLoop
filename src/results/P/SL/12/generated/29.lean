

theorem Topology.P1_P2_P3_univ {X : Type*} [TopologicalSpace X] :
    Topology.P1 (X := X) (Set.univ : Set X) ∧
      Topology.P2 (X := X) (Set.univ : Set X) ∧
      Topology.P3 (X := X) (Set.univ : Set X) := by
  have h₁ : Topology.P1 (X := X) (Set.univ : Set X) := by
    dsimp [Topology.P1]
    simp
  have h₂ : Topology.P2 (X := X) (Set.univ : Set X) := by
    dsimp [Topology.P2]
    simp
  have h₃ : Topology.P3 (X := X) (Set.univ : Set X) := by
    dsimp [Topology.P3]
    simp
  exact And.intro h₁ (And.intro h₂ h₃)