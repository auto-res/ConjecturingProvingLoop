

theorem Topology.P2_implies_P1_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : Topology.P2 (A := A)) : Topology.P1 A ∧ Topology.P3 A := by
  exact ⟨Topology.P2_implies_P1 h, Topology.P2_implies_P3 h⟩