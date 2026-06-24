

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P1 A := by
  intro hP2
  unfold Topology.P1 Topology.P2 at *
  intro x hx
  exact interior_subset (hP2 hx)