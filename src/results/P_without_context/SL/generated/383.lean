

theorem Topology.P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P3 A := by
  intro hP2
  unfold Topology.P2 Topology.P3 at *
  have hsubset : interior (closure (interior A)) ⊆ interior (closure A) := by
    have hsub : closure (interior A) ⊆ closure A := by
      have : interior A ⊆ A := interior_subset
      exact closure_mono this
    exact interior_mono hsub
  exact Set.Subset.trans hP2 hsubset