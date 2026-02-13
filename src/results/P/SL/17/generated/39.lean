

theorem Topology.P_properties_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_dense : Dense (interior A)) :
    Topology.P1 A ∧ Topology.P2 A ∧ Topology.P3 A := by
  have hP1 : Topology.P1 A := Topology.P1_of_dense_interior (A := A) h_dense
  have hP2 : Topology.P2 A := Topology.P2_of_dense_interior (A := A) h_dense
  have hP3 : Topology.P3 A := Topology.P2_implies_P3 (A := A) hP2
  exact ⟨hP1, ⟨hP2, hP3⟩⟩