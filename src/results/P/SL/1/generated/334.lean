

theorem Topology.dense_interior_closure_interior_of_dense_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior A) → Dense (interior (closure (interior A))) := by
  intro hDense
  -- We already have that `closure (interior (closure (interior A))) = univ`.
  have hEq :
      closure (interior (closure (interior A))) = (Set.univ : Set X) :=
    Topology.closure_interior_closure_interior_eq_univ_of_dense_interior
      (A := A) hDense
  -- Translate the closure equality into a density statement.
  exact (dense_iff_closure_eq).2 hEq