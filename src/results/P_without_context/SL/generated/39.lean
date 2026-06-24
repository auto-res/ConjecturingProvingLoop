

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P1 A := by
  intro hA
  unfold Topology.P1 Topology.P2 at *
  exact (Set.Subset.trans hA interior_subset)