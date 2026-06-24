

theorem P2_imp_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A : Set X) → Topology.P1 A := by
  intro h
  unfold Topology.P2 at h
  unfold Topology.P1
  exact subset_trans h (interior_subset)