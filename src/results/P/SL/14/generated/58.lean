

theorem Topology.P3_of_denseInterior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior A) → Topology.P3 A := by
  intro hDense
  have hP2 : Topology.P2 A :=
    Topology.P2_of_denseInterior (X := X) (A := A) hDense
  exact Topology.P2_implies_P3 (X := X) (A := A) hP2