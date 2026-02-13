

theorem Topology.P2_iff_P1_of_denseInterior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDense : Dense (interior A)) :
    Topology.P2 A ↔ Topology.P1 A := by
  have hP1 : Topology.P1 A :=
    Topology.P1_of_denseInterior (X := X) (A := A) hDense
  have hP2 : Topology.P2 A :=
    Topology.P2_of_denseInterior (X := X) (A := A) hDense
  exact ⟨fun _ => hP1, fun _ => hP2⟩