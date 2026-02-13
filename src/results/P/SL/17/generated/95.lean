

theorem Topology.P_properties_closure_of_dense {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDense : Dense A) :
    Topology.P1 (closure A) ∧ Topology.P2 (closure A) ∧ Topology.P3 (closure A) := by
  have hP1 : Topology.P1 (closure A) := Topology.P1_closure_of_dense (A := A) hDense
  have hP2 : Topology.P2 (closure A) := Topology.P2_closure_of_dense (A := A) hDense
  have hP3 : Topology.P3 (closure A) := Topology.P3_closure_of_dense (A := A) hDense
  exact ⟨hP1, ⟨hP2, hP3⟩⟩