

theorem Topology.P1_P2_P3_of_denseInterior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior A) →
      Topology.P1 A ∧ Topology.P2 A ∧ Topology.P3 A := by
  intro hDense
  have hP1 := Topology.P1_of_denseInterior (X := X) (A := A) hDense
  have hP2 := Topology.P2_of_denseInterior (X := X) (A := A) hDense
  have hP3 := Topology.P3_of_denseInterior (X := X) (A := A) hDense
  exact ⟨hP1, hP2, hP3⟩