

theorem P1_P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (A : Set X) → Topology.P2 A → Topology.P3 A := by
  intro _ hP2
  exact Topology.P2_implies_P3 (A := A) hP2