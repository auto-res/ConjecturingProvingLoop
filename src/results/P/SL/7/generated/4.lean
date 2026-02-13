

theorem IsOpen_P1_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) :
    Topology.P1 A ∧ Topology.P3 A := by
  have hP2 : Topology.P2 A := IsOpen_P2 hA
  exact Topology.P2_implies_P1_and_P3 hP2