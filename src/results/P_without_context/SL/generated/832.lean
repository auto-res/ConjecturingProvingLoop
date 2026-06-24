

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A := A) → Topology.P1 (A := A) := by
  intro h
  unfold Topology.P2 at h
  unfold Topology.P1
  exact h.trans interior_subset