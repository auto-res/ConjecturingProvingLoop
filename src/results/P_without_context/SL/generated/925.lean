

theorem Topology.P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : Topology.P2 A) : Topology.P1 A := by
  unfold Topology.P2 Topology.P1 at *
  exact fun x hx => interior_subset (h hx)