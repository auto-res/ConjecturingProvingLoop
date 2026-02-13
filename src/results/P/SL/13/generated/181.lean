

theorem Topology.dense_implies_all_P_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDense : Dense (A : Set X)) :
    (Topology.P1 (X := X) (closure (A : Set X))) ∧
      (Topology.P2 (X := X) (closure (A : Set X))) ∧
        (Topology.P3 (X := X) (closure (A : Set X))) := by
  have hP1 := Topology.dense_implies_P1_closure (X := X) (A := A) hDense
  have hP2 := Topology.dense_implies_P2_closure (X := X) (A := A) hDense
  have hP3 := Topology.dense_implies_P3_closure (X := X) (A := A) hDense
  exact ⟨hP1, hP2, hP3⟩