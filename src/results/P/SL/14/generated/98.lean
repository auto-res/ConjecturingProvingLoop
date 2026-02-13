

theorem Topology.interiorClosure_eq_univ_of_dense
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (A : Set X) → interior (closure A) = (Set.univ : Set X) := by
  intro hDense
  exact
    (Topology.dense_iff_interiorClosure_eq_univ
      (X := X) (A := A)).1 hDense