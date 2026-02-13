

theorem closure_interior_eq_univ_of_dense_P1
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 (A : Set X))
    (hDense : closure (A : Set X) = (Set.univ : Set X)) :
    closure (interior (A : Set X)) = (Set.univ : Set X) := by
  -- From `P1`, we know `closure (interior A) = closure A`.
  have hEq : closure (interior (A : Set X)) = closure A :=
    (Topology.P1_iff_closure_interior_eq_closure (A := A)).1 hP1
  -- Combine this with the density hypothesis to obtain the result.
  simpa [hDense] using hEq