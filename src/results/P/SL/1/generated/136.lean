

theorem Topology.P1_P2_P3_of_dense_interior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDense : Dense (interior A)) :
    Topology.P1 A ∧ Topology.P2 A ∧ Topology.P3 A := by
  have hP1 : Topology.P1 A :=
    Topology.P1_of_dense_interior (A := A) hDense
  have hP2 : Topology.P2 A :=
    Topology.P2_of_dense_interior (A := A) hDense
  have hP3 : Topology.P3 A :=
    Topology.P3_of_dense_interior (A := A) hDense
  exact And.intro hP1 (And.intro hP2 hP3)