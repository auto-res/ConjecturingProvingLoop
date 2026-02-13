

theorem Topology.P3_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDense : Dense (interior A)) : Topology.P3 A := by
  -- First, obtain P2 for `A` from the density of `interior A`
  have hP2 : Topology.P2 A := Topology.P2_of_dense_interior (A := A) hDense
  -- Then, derive P3 from P2
  exact Topology.P2_implies_P3 (A := A) hP2