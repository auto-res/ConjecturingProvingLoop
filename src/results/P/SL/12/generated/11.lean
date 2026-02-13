

theorem Topology.P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : Topology.P2 (X := X) A) :
    Topology.P3 (X := X) A := by
  exact (Topology.P2_implies_P1_and_P3 (X := X) (A := A) h).2