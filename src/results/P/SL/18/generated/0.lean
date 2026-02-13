

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P3 A := by
  intro hP2
  have hIntSubset : interior (closure (interior A)) ⊆ interior (closure A) := by
    have hClosSubset : closure (interior A) ⊆ closure A := by
      exact closure_mono interior_subset
    exact interior_mono hClosSubset
  exact Set.Subset.trans hP2 hIntSubset