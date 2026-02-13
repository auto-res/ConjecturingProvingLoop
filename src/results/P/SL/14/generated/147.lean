

theorem Topology.dense_iff_denseInteriorClosure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (A : Set X) ↔ Dense (interior (closure (A : Set X))) := by
  constructor
  · intro hDense
    exact Topology.denseInteriorClosure_of_dense (X := X) (A := A) hDense
  · intro hDenseInt
    exact Topology.dense_of_denseInteriorClosure (X := X) (A := A) hDenseInt