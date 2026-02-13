

theorem P1_iff_P2_of_dense {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDense : Dense A) : Topology.P1 A ↔ Topology.P2 A := by
  constructor
  · intro hP1
    exact Topology.P1_and_dense_implies_P2 (X := X) (A := A) hP1 hDense
  · intro hP2
    exact Topology.P2_implies_P1 (X := X) (A := A) hP2