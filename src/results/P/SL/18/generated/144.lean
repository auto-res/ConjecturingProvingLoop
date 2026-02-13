

theorem P3_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior (A : Set X)) → Topology.P3 A := by
  intro hDenseInt
  have hDenseA : Dense (A : Set X) :=
    Topology.dense_of_dense_interior (A := A) hDenseInt
  exact Topology.P3_of_dense (X := X) (A := A) hDenseA