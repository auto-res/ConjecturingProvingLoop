

theorem Topology.closure_interior_closure_eq_univ_of_P3
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP3 : Topology.P3 A) (h_dense : closure A = Set.univ) :
    closure (interior (closure A)) = Set.univ := by
  -- First, relate the two closures via `P3`.
  have h_eq :=
    Topology.closure_eq_closure_interior_closure_of_P3
      (X := X) (A := A) hP3
  -- Rewrite the equality so that the desired set appears on the left.
  have h_symm : closure (interior (closure A)) = closure A := by
    simpa using h_eq.symm
  -- Combine with the density hypothesis to reach the conclusion.
  simpa [h_dense] using h_symm