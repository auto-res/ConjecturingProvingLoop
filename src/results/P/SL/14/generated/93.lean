

theorem Topology.P3_iff_P1_of_dense
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDense : Dense (interior A)) :
    Topology.P3 A ↔ Topology.P1 A := by
  have hP1 : Topology.P1 A :=
    Topology.P1_of_denseInterior (X := X) (A := A) hDense
  have hP3 : Topology.P3 A :=
    Topology.P3_of_denseInterior (X := X) (A := A) hDense
  exact ⟨fun _ => hP1, fun _ => hP3⟩