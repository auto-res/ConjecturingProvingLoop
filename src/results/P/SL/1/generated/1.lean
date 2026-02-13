

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P3 A := by
  intro hA
  dsimp [Topology.P2, Topology.P3] at hA ⊢
  have hsubset : interior (closure (interior A)) ⊆ interior (closure A) := by
    have hclosure : closure (interior A) ⊆ closure A := by
      exact closure_mono interior_subset
    exact interior_mono hclosure
  exact Set.Subset.trans hA hsubset