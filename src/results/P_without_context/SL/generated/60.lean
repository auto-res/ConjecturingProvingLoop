

theorem Topology.P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : Topology.P2 (A := A)) : Topology.P1 (A := A) := by
  dsimp [Topology.P2] at h
  dsimp [Topology.P1]
  intro x hx
  exact interior_subset (h hx)