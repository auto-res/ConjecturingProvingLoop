

theorem Topology.closure_interior_eq_closure_of_dense_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} (hDense : Dense (interior A)) :
    closure (interior A) = closure A := by
  -- Obtain `P2` for `A` from the density of its interior.
  have hP2 : Topology.P2 A := Topology.P2_of_dense_interior (A := A) hDense
  -- Use the existing lemma that equates the two closures under `P2`.
  exact Topology.closure_interior_eq_closure_of_P2 (A := A) hP2