

theorem P2_of_P1_and_dense {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 A) (hDense : closure (A : Set X) = (Set.univ : Set X)) :
    Topology.P2 A := by
  -- `P1` yields an equality of closures.
  have hEq : closure (interior A) = closure A := by
    simpa using
      (Topology.closure_eq_closure_interior_of_P1 (A := A) hP1).symm
  -- Combine with the density assumption to make `closure (interior A)` the whole space.
  have hDenseInt : closure (interior A) = (Set.univ : Set X) := by
    simpa [hEq] using hDense
  -- Invoke the existing lemma that turns this density into `P2`.
  exact Topology.P2_of_dense_interior (A := A) hDenseInt