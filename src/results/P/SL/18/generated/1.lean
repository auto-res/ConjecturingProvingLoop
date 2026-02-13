

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P1 A := by
  intro hP2
  have hIntSubset : interior (closure (interior A)) ⊆ closure (interior A) := by
    exact interior_subset
  exact Set.Subset.trans hP2 hIntSubset