

theorem P123_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDenseInt : Dense (interior (A : Set X))) :
    Topology.P1 A ∧ Topology.P2 A ∧ Topology.P3 A := by
  have hP1 : Topology.P1 A := Topology.P1_of_dense_interior (A := A) hDenseInt
  have hP2 : Topology.P2 A := Topology.P2_of_dense_interior (A := A) hDenseInt
  have hP3 : Topology.P3 A := Topology.P3_of_dense_interior (A := A) hDenseInt
  exact ⟨hP1, hP2, hP3⟩