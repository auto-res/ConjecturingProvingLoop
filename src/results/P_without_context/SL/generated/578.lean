

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P3 A := by
  intro hP2
  have h_int_subset : interior (closure (interior A)) ⊆ interior (closure A) := by
    have h_closure_subset : closure (interior A) ⊆ closure A := by
      have h_interior_subset : interior A ⊆ A := interior_subset
      exact closure_mono h_interior_subset
    exact interior_mono h_closure_subset
  exact subset_trans hP2 h_int_subset