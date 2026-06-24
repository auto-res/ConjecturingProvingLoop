

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P3 A := by
  intro hP2
  dsimp [Topology.P2, Topology.P3] at hP2 ⊢
  have hsubset : interior (closure (interior A)) ⊆ interior (closure A) := by
    apply interior_mono
    exact closure_mono interior_subset
  exact Set.Subset.trans hP2 hsubset