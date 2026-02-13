

theorem Topology.P2_iff_P3_of_denseInterior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDense : Dense (interior A)) :
    Topology.P2 A ↔ Topology.P3 A := by
  have h₁ := Topology.P2_iff_P1_of_denseInterior (X := X) (A := A) hDense
  have h₂ := Topology.P3_iff_P1_of_dense (X := X) (A := A) hDense
  simpa using h₁.trans h₂.symm