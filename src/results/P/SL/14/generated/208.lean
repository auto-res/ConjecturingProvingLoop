

theorem Topology.closure_satisfies_P1_P2_P3_of_dense
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDense : Dense (A : Set X)) :
    Topology.P1 (closure (A : Set X)) ∧
      Topology.P2 (closure (A : Set X)) ∧
      Topology.P3 (closure (A : Set X)) := by
  have hP1 : Topology.P1 (closure (A : Set X)) :=
    Topology.closure_has_P1_of_dense (X := X) (A := A) hDense
  have hP2 : Topology.P2 (closure (A : Set X)) :=
    Topology.P2_closure_of_dense (X := X) (A := A) hDense
  have hP3 : Topology.P3 (closure (A : Set X)) :=
    Topology.P3_closure_of_dense (X := X) (A := A) hDense
  exact ⟨hP1, hP2, hP3⟩