

theorem P2_imp_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A : Set X) → Topology.P3 A := by
  intro hP2
  dsimp [Topology.P2, Topology.P3] at *
  have h_sub : interior (closure (interior A)) ⊆ interior (closure A) := by
    have h_closure : closure (interior A) ⊆ closure A := by
      exact closure_mono interior_subset
    exact interior_mono h_closure
  exact Set.Subset.trans hP2 h_sub