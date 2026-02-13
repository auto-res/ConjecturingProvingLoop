

theorem Topology.dense_closure_of_dense_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior A) → Dense (closure A) := by
  intro hDenseInt
  -- First, use density of `interior A` to see that `closure A = univ`.
  have hEq : closure A = (Set.univ : Set X) :=
    Topology.closure_eq_univ_of_dense_interior (A := A) hDenseInt
  -- Taking the closure once more does not change the set.
  have hEq' : closure (closure A) = (Set.univ : Set X) := by
    simpa [closure_closure] using hEq
  -- Translate the equality into a density statement.
  exact (dense_iff_closure_eq).2 hEq'