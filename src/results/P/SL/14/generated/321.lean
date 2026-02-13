

theorem Topology.isClosed_dense_satisfies_P1_P2_P3
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) (hDense : Dense (A : Set X)) :
    Topology.P1 A ∧ Topology.P2 A ∧ Topology.P3 A := by
  have hP1 : Topology.P1 A :=
    Topology.P1_of_isClosed_and_dense (X := X) (A := A) hA_closed hDense
  have hP2 : Topology.P2 A :=
    Topology.P2_of_isClosed_and_dense (X := X) (A := A) hA_closed hDense
  have hP3 : Topology.P3 A :=
    Topology.P3_of_isClosed_and_dense (X := X) (A := A) hA_closed hDense
  exact ⟨hP1, hP2, hP3⟩