

theorem Topology.closed_dense_interior_eq_univ {X : Type*} [TopologicalSpace X]
    {A : Set X} (hClosed : IsClosed A) (hDenseInt : Dense (interior A)) :
    A = (Set.univ : Set X) := by
  -- The density of `interior A` implies `closure A = univ`.
  have hClosure : closure A = (Set.univ : Set X) :=
    Topology.closure_eq_univ_of_dense_interior (A := A) hDenseInt
  -- Since `A` is closed, `closure A = A`; combine the equalities.
  simpa [hClosed.closure_eq] using hClosure