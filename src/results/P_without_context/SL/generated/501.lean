

theorem Topology.P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P3 A := by
  intro hP2
  have h_subset : interior (closure (interior A)) ⊆ interior (closure A) := by
    have h_closure : closure (interior A) ⊆ closure A := by
      have h_int : (interior A : Set X) ⊆ A := interior_subset
      exact closure_mono h_int
    exact interior_mono h_closure
  exact Set.Subset.trans hP2 h_subset