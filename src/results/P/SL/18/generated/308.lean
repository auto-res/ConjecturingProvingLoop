

theorem P123_closure_of_dense {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (A : Set X) →
      Topology.P1 (closure (A : Set X)) ∧
        Topology.P2 (closure (A : Set X)) ∧
        Topology.P3 (closure (A : Set X)) := by
  intro hDense
  have hP1 := Topology.P1_closure_of_dense (A := A) hDense
  have hP2 := Topology.P2_closure_of_dense (A := A) hDense
  have hP3 := Topology.P3_closure_of_dense (A := A) hDense
  exact ⟨hP1, hP2, hP3⟩