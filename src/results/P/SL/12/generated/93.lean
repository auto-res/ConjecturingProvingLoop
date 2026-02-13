

theorem Topology.P1_P2_P3_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : closure (interior A : Set X) = Set.univ) :
    Topology.P1 (X := X) A ∧ Topology.P2 (X := X) A ∧ Topology.P3 (X := X) A := by
  have hP1 : Topology.P1 (X := X) A :=
    Topology.P1_of_dense_interior (X := X) (A := A) hA
  have hP2 : Topology.P2 (X := X) A :=
    Topology.P2_of_dense_interior (X := X) (A := A) hA
  have hP3 : Topology.P3 (X := X) A :=
    Topology.P3_of_dense_interior (X := X) (A := A) hA
  exact And.intro hP1 (And.intro hP2 hP3)