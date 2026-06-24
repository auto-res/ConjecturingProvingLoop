

theorem P2_implies_P1_and_P3
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → (Topology.P1 A ∧ Topology.P3 A) := by
  intro hP2
  -- first implication P2 → P1
  have hP1 : Topology.P1 A := by
    dsimp [Topology.P1, Topology.P2] at *
    exact subset_trans hP2 interior_subset
  -- second implication P2 → P3
  have hP3 : Topology.P3 A := by
    dsimp [Topology.P2] at hP2
    dsimp [Topology.P3]
    have hcl : closure (interior A) ⊆ closure A := by
      have : interior A ⊆ A := interior_subset
      exact closure_mono this
    have hint : interior (closure (interior A)) ⊆ interior (closure A) :=
      interior_mono hcl
    exact subset_trans hP2 hint
  exact And.intro hP1 hP3