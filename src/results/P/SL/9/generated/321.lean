

theorem Topology.closed_dense_eq_univ {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_closed : IsClosed A) (h_dense : Dense (A : Set X)) :
    A = (Set.univ : Set X) := by
  -- For closed sets, the closure is the set itself.
  have h_closure_self : closure (A : Set X) = A := h_closed.closure_eq
  -- For dense sets, the closure is the whole space.
  have h_closure_univ : closure (A : Set X) = (Set.univ : Set X) := h_dense.closure_eq
  -- Combine the two equalities.
  simpa [h_closure_self] using h_closure_univ