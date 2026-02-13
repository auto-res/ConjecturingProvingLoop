

theorem Topology.P1_closure_of_dense {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDense : Dense A) : Topology.P1 (closure A) := by
  -- `A` is dense, so its closure is the whole space.
  have h_closure : closure A = (Set.univ : Set X) := hDense.closure_eq
  -- We already know that `P1` holds for `Set.univ`.
  have hP1_univ : Topology.P1 (Set.univ : Set X) := Topology.P1_univ (X := X)
  -- Rewriting along the equality gives the desired result.
  simpa [h_closure] using hP1_univ