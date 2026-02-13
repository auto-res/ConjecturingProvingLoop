

theorem Topology.P1_iff_P3_of_dense_interior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : Dense (interior A)) :
    Topology.P1 A ↔ Topology.P3 A := by
  constructor
  · intro _; exact Topology.P3_of_dense_interior (A := A) h
  · intro _; exact Topology.P1_of_dense_interior (A := A) h