

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (X := X) A → Topology.P3 (X := X) A := by
  intro hP2
  unfold Topology.P2 at hP2
  unfold Topology.P3
  have h_subset : interior (closure (interior A)) ⊆ interior (closure A) := by
    have h_closure : closure (interior A) ⊆ closure A := by
      exact closure_mono interior_subset
    exact interior_mono h_closure
  exact subset_trans hP2 h_subset