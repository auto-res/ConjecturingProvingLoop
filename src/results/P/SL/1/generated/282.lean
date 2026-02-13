

theorem Topology.dense_closure_of_dense
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense A → Dense (closure A) := by
  intro hDense
  exact (Topology.dense_closure_iff_dense (A := A)).mpr hDense