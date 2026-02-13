

theorem Topology.denseInterior_implies_all_P {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Dense (interior (A : Set X)) →
      (Topology.P1 (X:=X) A) ∧
        (Topology.P2 (X:=X) A) ∧
          (Topology.P3 (X:=X) A) := by
  intro hDense
  have hP1 := Topology.denseInterior_implies_P1 (X := X) (A := A) hDense
  have hP2 := Topology.denseInterior_implies_P2 (X := X) (A := A) hDense
  have hP3 := Topology.denseInterior_implies_P3 (X := X) (A := A) hDense
  exact ⟨hP1, hP2, hP3⟩