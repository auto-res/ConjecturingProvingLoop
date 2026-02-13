

theorem Topology.univ_satisfies_P1_P2_P3 {X : Type*} [TopologicalSpace X] :
    Topology.P1 (X := X) (Set.univ : Set X) ∧
    Topology.P2 (X := X) (Set.univ : Set X) ∧
    Topology.P3 (X := X) (Set.univ : Set X) := by
  -- Prove `P1`.
  have hP1 : Topology.P1 (X := X) (Set.univ : Set X) := by
    dsimp [Topology.P1]
    intro x hx
    simpa [closure_univ, interior_univ] using hx
  -- Prove `P2`.
  have hP2 : Topology.P2 (X := X) (Set.univ : Set X) := by
    dsimp [Topology.P2]
    intro x hx
    simpa [closure_univ, interior_univ] using hx
  -- Prove `P3`.
  have hP3 : Topology.P3 (X := X) (Set.univ : Set X) := by
    dsimp [Topology.P3]
    intro x hx
    simpa [closure_univ, interior_univ] using hx
  exact ⟨hP1, hP2, hP3⟩