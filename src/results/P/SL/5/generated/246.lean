

theorem P3_iff_P2_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : interior (A : Set X) = Set.univ) :
    Topology.P3 (X := X) A ↔ Topology.P2 (X := X) A := by
  constructor
  · intro _hP3
    exact Topology.P2_of_dense_interior (X := X) (A := A) h
  · intro _hP2
    exact Topology.P3_of_dense_interior (X := X) (A := A) h