

theorem P3_iff_P2_of_denseInterior {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDense : Dense (interior A)) :
    Topology.P3 A ↔ Topology.P2 A := by
  -- From the density of `interior A` we immediately obtain `P1 A`.
  have hP1 : Topology.P1 A :=
    Topology.denseInterior_implies_P1 (X := X) (A := A) hDense
  constructor
  · intro hP3
    exact Topology.P3_and_P1_implies_P2 (X := X) (A := A) hP3 hP1
  · intro hP2
    exact Topology.P2_implies_P3 (X := X) (A := A) hP2