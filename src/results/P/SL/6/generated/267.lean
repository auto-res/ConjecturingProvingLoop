

theorem closure_interior_eq_univ_of_dense_P2
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A : Set X) →
      closure (A : Set X) = (Set.univ : Set X) →
      closure (interior (A : Set X)) = (Set.univ : Set X) := by
  intro hP2 hDense
  -- From `P2`, we know the closures of `A` and `interior A` coincide.
  have hEq : closure (interior (A : Set X)) = closure A :=
    Topology.P2_implies_closure_interior_eq_closure (A := A) hP2
  -- Combine this with the density hypothesis.
  simpa [hDense] using hEq.trans hDense