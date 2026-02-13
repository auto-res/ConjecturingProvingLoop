

theorem Topology.closed_dense_eq_univ {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed (A : Set X)) (hA_dense : Dense (A : Set X)) :
    (A : Set X) = (Set.univ : Set X) := by
  -- The closure of a closed set is itself.
  have h_closure_closed : closure (A : Set X) = A := hA_closed.closure_eq
  -- The closure of a dense set is the whole space.
  have h_closure_dense : closure (A : Set X) = (Set.univ : Set X) := hA_dense.closure_eq
  -- Combine the two equalities.
  simpa [h_closure_closed] using h_closure_dense