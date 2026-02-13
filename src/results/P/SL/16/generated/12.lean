

theorem Topology.empty_satisfies_P1_P2_P3 {X : Type*} [TopologicalSpace X] :
    Topology.P1 (X := X) (∅ : Set X) ∧
    Topology.P2 (X := X) (∅ : Set X) ∧
    Topology.P3 (X := X) (∅ : Set X) := by
  have hP1 : Topology.P1 (X := X) (∅ : Set X) := by
    dsimp [Topology.P1]
    intro x hx
    cases hx
  have hP2 : Topology.P2 (X := X) (∅ : Set X) := by
    dsimp [Topology.P2]
    intro x hx
    cases hx
  have hP3 : Topology.P3 (X := X) (∅ : Set X) := by
    dsimp [Topology.P3]
    intro x hx
    cases hx
  exact ⟨hP1, hP2, hP3⟩