

theorem P2_iff_P3_of_dense_interior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDenseInt : Dense (interior (A : Set X))) :
    Topology.P2 A ↔ Topology.P3 A := by
  constructor
  · intro hP2
    exact Topology.P2_implies_P3 hP2
  · intro _hP3
    exact Topology.P2_of_dense_interior (A := A) hDenseInt