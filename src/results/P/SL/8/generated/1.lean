

theorem P2_imp_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P3 A := by
  intro hP2
  dsimp [Topology.P2, Topology.P3] at hP2 ⊢
  have hsubset : interior (closure (interior A)) ⊆ interior (closure A) := by
    have hcl : closure (interior A) ⊆ closure A := by
      have : interior A ⊆ A := interior_subset
      exact closure_mono this
    exact interior_mono hcl
  exact Set.Subset.trans hP2 hsubset