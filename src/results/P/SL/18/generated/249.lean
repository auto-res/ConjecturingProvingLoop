

theorem dense_interior_closure_of_dense
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (A : Set X) → Dense (interior (closure (A : Set X))) := by
  intro hDense
  -- Translate the density of `A` into a closure equality.
  have hEq : closure (interior (closure (A : Set X))) = (Set.univ : Set X) :=
    (Topology.dense_iff_closure_interior_closure_eq_univ (A := A)).1 hDense
  -- Reinterpret the equality as density of `interior (closure A)`.
  exact
    (Topology.dense_iff_closure_eq_univ
        (A := interior (closure (A : Set X)))).2 hEq