

theorem Topology.P2_closure_of_dense {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense A → Topology.P2 (closure A) := by
  intro hDense
  -- Since `A` is dense, its closure is the whole space.
  have hEq : closure A = (Set.univ : Set X) := by
    simpa using hDense.closure_eq
  -- Rewriting with `hEq`, the statement reduces to `P2` for `Set.univ`,
  -- which is already established.
  simpa [hEq] using (P2_univ (X := X))