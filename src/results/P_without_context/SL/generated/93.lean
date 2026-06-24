

theorem Topology.P2_imp_P1_and_P3
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A : Set X) → Topology.P1 A ∧ Topology.P3 A := by
  intro hP2
  dsimp [Topology.P2] at hP2
  -- P1 follows since interior ⊆ closure
  have h1 : Topology.P1 A := by
    dsimp [Topology.P1]
    exact Set.Subset.trans hP2 (interior_subset)
  -- P3 follows by monotonicity of closure and interior
  have h2 : Topology.P3 A := by
    dsimp [Topology.P3]
    have hcl : closure (interior A) ⊆ closure A :=
      closure_mono (interior_subset : interior A ⊆ A)
    exact Set.Subset.trans hP2 (interior_mono hcl)
  exact And.intro h1 h2