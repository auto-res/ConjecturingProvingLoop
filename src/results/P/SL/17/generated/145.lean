

theorem Topology.P2_closure_interior_of_dense_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} (hDense : Dense (interior A)) :
    Topology.P2 (closure (interior A)) := by
  -- Because `interior A` is dense, its closure is the whole space.
  have hEq : closure (interior A) = (Set.univ : Set X) := hDense.closure_eq
  -- `P2` holds for `Set.univ`; rewrite using `hEq`.
  simpa [hEq] using (Topology.P2_univ (X := X))