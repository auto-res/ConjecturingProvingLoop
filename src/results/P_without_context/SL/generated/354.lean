

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A := A) → Topology.P1 (A := A) := by
  unfold Topology.P2 Topology.P1
  intro h
  exact subset_trans h interior_subset