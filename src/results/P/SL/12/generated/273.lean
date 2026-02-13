

theorem Topology.P1_iff_P3_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_dense : closure (interior (A : Set X)) = (Set.univ : Set X)) :
    Topology.P1 (X := X) A ↔ Topology.P3 (X := X) A := by
  constructor
  · intro _hP1
    exact Topology.P3_of_dense_interior (X := X) (A := A) h_dense
  · intro _hP3
    exact Topology.P1_of_dense_interior (X := X) (A := A) h_dense