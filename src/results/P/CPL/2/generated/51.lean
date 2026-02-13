

theorem P2_iff_P3_of_dense {X : Type*} [TopologicalSpace X] {A : Set X} (hA : Dense (interior A)) : Topology.P2 (X:=X) A ↔ Topology.P3 (X:=X) A := by
  constructor
  · intro hP2
    exact Topology.P3_of_P2 (A := A) hP2
  · intro _hP3
    exact Topology.P2_of_dense_interior (X := X) (A := A) hA