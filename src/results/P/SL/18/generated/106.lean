

theorem P3_of_interior_closure_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (A : Set X)) = Set.univ → Topology.P3 A := by
  intro hInt
  -- From the equality of interiors, infer density of `A`.
  have hDense : Dense (A : Set X) :=
    Topology.dense_of_interior_closure_eq_univ (A := A) hInt
  -- Density implies property `P3`.
  exact Topology.P3_of_dense (X := X) hDense