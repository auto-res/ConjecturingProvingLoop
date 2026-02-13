

theorem P3_closure_interior_of_dense_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Dense (interior (A : Set X)) →
      Topology.P3 (closure (interior (A : Set X))) := by
  intro hDenseInt
  simpa using
    (Topology.P3_closure_of_dense (A := interior (A : Set X)) hDenseInt)