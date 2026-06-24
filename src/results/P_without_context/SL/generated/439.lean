

theorem P2_imp_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P1 A := by
  intro hA
  unfold Topology.P2 Topology.P1 at *
  have hsubset : interior (closure (interior A)) ⊆ closure (interior A) := by
    simpa using interior_subset
  exact Set.Subset.trans hA hsubset