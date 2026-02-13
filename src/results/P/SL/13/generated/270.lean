

theorem Topology.all_P_closed_dense {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed (A : Set X)) (hA_dense : Dense (A : Set X)) :
    Topology.P1 (X := X) A ∧ Topology.P2 (X := X) A ∧ Topology.P3 (X := X) A := by
  have hP1 : Topology.P1 (X := X) A :=
    Topology.closed_dense_implies_P1 (X := X) (A := A) hA_closed hA_dense
  have hP2 : Topology.P2 (X := X) A :=
    Topology.closed_dense_implies_P2 (X := X) (A := A) hA_closed hA_dense
  have hP3 : Topology.P3 (X := X) A :=
    Topology.closed_dense_implies_P3 (X := X) (A := A) hA_closed hA_dense
  exact ⟨hP1, hP2, hP3⟩