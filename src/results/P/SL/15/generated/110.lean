

theorem denseInterior_implies_P2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior A) → Topology.P2 A := by
  intro hDense
  have hP1 : Topology.P1 A :=
    Topology.denseInterior_implies_P1 (X := X) (A := A) hDense
  have hP3 : Topology.P3 A :=
    Topology.denseInterior_implies_P3 (X := X) (A := A) hDense
  exact (Topology.P3_and_P1_implies_P2 (X := X) (A := A)) hP3 hP1