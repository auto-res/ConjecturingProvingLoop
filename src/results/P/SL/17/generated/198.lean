

theorem Topology.P3_of_dense_interior_alt {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDense : Dense (interior A)) : Topology.P3 A := by
  -- We already have `P3_of_dense_interior`, use it directly.
  simpa using (Topology.P3_of_dense_interior (A := A) hDense)