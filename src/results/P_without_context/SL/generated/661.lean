

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P1 A := by
  intro hP2
  have h_subset : interior (closure (interior A)) ⊆ closure (interior A) := by
    simpa using interior_subset
  exact subset_trans hP2 h_subset