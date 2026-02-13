

theorem Topology.P2_closure_interior_of_dense_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior A) → Topology.P2 (closure (interior A)) := by
  intro hDense
  -- Since `interior A` is dense, its closure is the whole space.
  have hEq : closure (interior A) = (Set.univ : Set X) := by
    simpa using hDense.closure_eq
  -- Rewriting with `hEq`, the statement reduces to `P2` for `Set.univ`,
  -- which is already established.
  simpa [hEq] using (P2_univ (X := X))